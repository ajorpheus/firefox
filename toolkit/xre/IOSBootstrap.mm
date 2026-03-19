/* clang-format off */
/* -*- Mode: Objective-C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*- */
/* clang-format on */
/* vim: set ts=8 sts=2 et sw=2 tw=80: */
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this file,
 * You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "GeckoView/IOSBootstrap.h"
#include "GeckoView/GeckoViewSwiftSupport.h"

#include "mozilla/Bootstrap.h"
#include "mozilla/DarwinObjectPtr.h"
#include "mozilla/GeckoArgs.h"
#include "mozilla/widget/GeckoViewRuntimeSupport.h"
#include "mozilla/widget/GeckoViewSupport.h"
#include "nsDebug.h"
#include "nsPrintfCString.h"
#include "XREChildData.h"
#include "js/Initialization.h"

#include <errno.h>
#include <libkern/OSCacheControl.h>
#include <mach/mach.h>
#include <poll.h>
#if __has_include(<ptrauth.h>)
#  include <ptrauth.h>
#endif
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <sys/mman.h>
#include <unistd.h>

#include "application.ini.h"

static id<SwiftGeckoViewRuntime> gRuntime;

id<SwiftGeckoViewRuntime> mozilla::widget::GetSwiftRuntime() {
  return gRuntime;
}

static id<GeckoProcessExtension> gCurrentProcessExtension;
static int gExecutableJITReadyFd = -1;
static sigjmp_buf gExecutableProbeSignalJump;
static volatile sig_atomic_t gExecutableProbeSignal = 0;
static volatile sig_atomic_t gExecutableProbeSignalCode = 0;
static volatile uintptr_t gExecutableProbeFaultAddress = 0;

static void ExecutableProbeSignalHandler(int signalNumber, siginfo_t* info,
                                         void* context) {
  (void)context;
  gExecutableProbeSignal = signalNumber;
  gExecutableProbeSignalCode = info ? info->si_code : 0;
  gExecutableProbeFaultAddress =
      info ? reinterpret_cast<uintptr_t>(info->si_addr) : 0;
  siglongjmp(gExecutableProbeSignalJump, 1);
}

id<GeckoProcessExtension> mozilla::widget::GetCurrentProcessExtension() {
  return gCurrentProcessExtension;
}

// REYNARD: Request an RX JIT region from the debugger-backed iOS allocation
// path and return the resulting executable address through x0.
#if defined(__aarch64__)
__attribute__((noinline, optnone, naked)) static void*
DebuggerAllocateExecutableRegionTrap(void* aAddress, size_t aSize) {
  asm volatile("mov x16, #1\n"
               "brk #0xf00d\n"
               "ret\n");
}
#endif

static void* RequestDebuggerAllocateExecutableRegion(size_t aSize) {
#if defined(__aarch64__)
  return DebuggerAllocateExecutableRegionTrap(nullptr, aSize);
#else
  (void)aSize;
  return nullptr;
#endif
}

static bool CanAllocateExecutableJitPage(int* aErrno) {
  const size_t pageSize = static_cast<size_t>(getpagesize());
  void* reservation = RequestDebuggerAllocateExecutableRegion(pageSize);
  if (!reservation) {
    if (aErrno) {
      *aErrno = ENOMEM;
    }
    return false;
  }

  vm_address_t writableAlias = 0;
  vm_prot_t currentProtection = VM_PROT_READ | VM_PROT_WRITE;
  vm_prot_t maxProtection = VM_PROT_READ | VM_PROT_WRITE | VM_PROT_EXECUTE;
  kern_return_t remapResult = vm_remap(
      mach_task_self(), &writableAlias, pageSize, 0, VM_FLAGS_ANYWHERE,
      mach_task_self(), reinterpret_cast<vm_address_t>(reservation), false,
      &currentProtection, &maxProtection, VM_INHERIT_SHARE);
  if (remapResult != KERN_SUCCESS) {
    vm_deallocate(mach_task_self(), reinterpret_cast<vm_address_t>(reservation),
                  pageSize);
    if (aErrno) {
      *aErrno = int(remapResult);
    }
    return false;
  }

  if (vm_protect(mach_task_self(), writableAlias, pageSize, false,
                 VM_PROT_READ | VM_PROT_WRITE) != KERN_SUCCESS) {
    vm_deallocate(mach_task_self(), writableAlias, pageSize);
    vm_deallocate(mach_task_self(), reinterpret_cast<vm_address_t>(reservation),
                  pageSize);
    if (aErrno) {
      *aErrno = EPERM;
    }
    return false;
  }

  uint32_t* code = reinterpret_cast<uint32_t*>(writableAlias);
  code[0] = 0xD503245F;  // bti c
  code[1] = 0x52800540;  // mov w0, #42
  code[2] = 0xD65F03C0;  // ret

  if (vm_protect(mach_task_self(), writableAlias, pageSize, false,
                 VM_PROT_READ) != KERN_SUCCESS) {
    vm_deallocate(mach_task_self(), writableAlias, pageSize);
    vm_deallocate(mach_task_self(), reinterpret_cast<vm_address_t>(reservation),
                  pageSize);
    if (aErrno) {
      *aErrno = EPERM;
    }
    return false;
  }

  // REYNARD: Flush the writable alias back to the executable view before the
  // child branches into freshly generated code.
    sys_cache_control(kCacheFunctionPrepareForExecution, reservation,
          sizeof(uint32_t) * 3);

  vm_address_t writableAliasToFree = writableAlias;
  writableAlias = 0;
  if (vm_deallocate(mach_task_self(), writableAliasToFree, pageSize) !=
      KERN_SUCCESS) {
    vm_deallocate(mach_task_self(), reinterpret_cast<vm_address_t>(reservation),
                  pageSize);
    if (aErrno) {
      *aErrno = EPERM;
    }
    return false;
  }

  using ProbeFunction = int (*)();
  ProbeFunction probe = reinterpret_cast<ProbeFunction>(reservation);
#if __has_feature(ptrauth_calls)
  probe = reinterpret_cast<ProbeFunction>(
      ptrauth_sign_unauthenticated(reinterpret_cast<void*>(reservation),
                                   ptrauth_key_function_pointer, 0));
#endif
  const int handledSignals[] = {SIGBUS, SIGSEGV, SIGILL, SIGTRAP};
  struct sigaction newAction;
  memset(&newAction, 0, sizeof(newAction));
  sigemptyset(&newAction.sa_mask);
  newAction.sa_sigaction = ExecutableProbeSignalHandler;
  newAction.sa_flags = SA_SIGINFO;
  struct sigaction oldActions[std::size(handledSignals)];
  for (size_t index = 0; index < std::size(handledSignals); index++) {
    sigaction(handledSignals[index], &newAction, &oldActions[index]);
  }

  gExecutableProbeSignal = 0;
  gExecutableProbeSignalCode = 0;
  gExecutableProbeFaultAddress = 0;
  int result = 0;
  bool handledSignal = false;
  if (sigsetjmp(gExecutableProbeSignalJump, 1) == 0) {
    result = probe();
  } else {
    handledSignal = true;
  }
  for (size_t index = 0; index < std::size(handledSignals); index++) {
    sigaction(handledSignals[index], &oldActions[index], nullptr);
  }

  if (handledSignal) {
    fprintf(stderr,
            "REYNARD_DEBUG: Child executable probe signal, pid=%d, signal=%d, code=%d, addr=0x%llx\n",
            getpid(), gExecutableProbeSignal, gExecutableProbeSignalCode,
            static_cast<unsigned long long>(gExecutableProbeFaultAddress));
    fflush(stderr);
    vm_deallocate(mach_task_self(), reinterpret_cast<vm_address_t>(reservation),
                  pageSize);
    if (aErrno) {
      *aErrno = EFAULT;
    }
    return false;
  }
  vm_deallocate(mach_task_self(), reinterpret_cast<vm_address_t>(reservation),
                pageSize);

  if (result != 42) {
    if (aErrno) {
      *aErrno = EIO;
    }
    return false;
  }

  if (aErrno) {
    *aErrno = 0;
  }
  return true;
}

// REYNARD: Wait for the parent process to finish the per-pid JIT attach path
// before allowing the content child to keep SpiderMonkey JIT enabled.
static bool WaitForParentExecutableJITReady(int* aErrno) {
  if (gExecutableJITReadyFd == -1) {
    if (aErrno) {
      *aErrno = ENOENT;
    }
    return false;
  }

  pollfd descriptor = {
      .fd = gExecutableJITReadyFd,
      .events = POLLIN,
      .revents = 0,
  };

  const int pollResult = poll(&descriptor, 1, 5000);
  if (pollResult <= 0) {
    const int resultErrno = pollResult == 0 ? ETIMEDOUT : errno;
    close(gExecutableJITReadyFd);
    gExecutableJITReadyFd = -1;
    if (aErrno) {
      *aErrno = resultErrno;
    }
    return false;
  }

  uint8_t status = 0;
  const ssize_t bytesRead = read(gExecutableJITReadyFd, &status, sizeof(status));
  const int readErrno = bytesRead == sizeof(status) ? 0 : errno;
  close(gExecutableJITReadyFd);
  gExecutableJITReadyFd = -1;

  if (bytesRead != sizeof(status)) {
    if (aErrno) {
      *aErrno = readErrno;
    }
    return false;
  }

  if (!status) {
    if (aErrno) {
      *aErrno = EPERM;
    }
    return false;
  }

  if (aErrno) {
    *aErrno = 0;
  }
  return true;
}

static bool WaitForExecutableJITReady(int* aErrno) {
  if (!WaitForParentExecutableJITReady(aErrno)) {
    return false;
  }

  constexpr unsigned kMaxAttempts = 100;
  constexpr useconds_t kRetryDelayUs = 100000;

  for (unsigned attempt = 0; attempt < kMaxAttempts; ++attempt) {
    if (CanAllocateExecutableJitPage(aErrno)) {
      return true;
    }
    usleep(kRetryDelayUs);
  }

  return false;
}

void mozilla::widget::NotifyChildProcessStarted(int32_t aPid,
                                                const char* aProcessType) {
  // REYNARD: Forward child process launch notifications to the Swift host so
  // it can attach the JIT debugger path as soon as the pid is
  // known in the parent process, while still letting the app distinguish the
  // Gecko child process type.
  if (!gRuntime) {
    return;
  }

  NSString* processType = @"invalid";
  if (aProcessType) {
    processType = [NSString stringWithUTF8String:aProcessType];
    if (!processType) {
      processType = @"invalid";
    }
  }

  if ([gRuntime respondsToSelector:@selector(childProcessDidStartWithPID:processType:)]) {
    [gRuntime childProcessDidStartWithPID:aPid processType:processType];
  }
}

int MainProcessInit(int aArgc, char** aArgv,
                    id<SwiftGeckoViewRuntime> aRuntime) {
  auto bootstrap = mozilla::GetBootstrap();
  if (bootstrap.isErr()) {
    printf_stderr("Couldn't load XPCOM.\n");
    return 255;
  }

  gRuntime = [aRuntime retain];

  mozilla::BootstrapConfig config;
  config.appData = &sAppData;
  config.appDataPath = nullptr;

  return bootstrap.inspect()->XRE_main(aArgc, aArgv, config);
}

static void HandleBootstrapMessage(xpc_object_t aEvent);

void ChildProcessInit(xpc_connection_t aXpcConnection,
                      id<GeckoProcessExtension> aProcess,
                      id<SwiftGeckoViewRuntime> aRuntime) {
  gCurrentProcessExtension = aProcess;
  gRuntime = [aRuntime retain];
  static std::atomic<bool> geckoViewStarted = false;

  xpc_connection_set_event_handler(aXpcConnection, [](xpc_object_t aEvent) {
    xpc_type_t type = xpc_get_type(aEvent);
    if (type != XPC_TYPE_DICTIONARY) {
      NSLog(@"[%d] Received unexpected XPC event type: %s\n", getpid(),
            xpc_type_get_name(type));
      if (!geckoViewStarted && type == XPC_TYPE_ERROR &&
          (aEvent == XPC_ERROR_CONNECTION_INVALID ||
           aEvent == XPC_ERROR_TERMINATION_IMMINENT)) {
        // FIXME: handle this more gracefully?
        MOZ_CRASH("Received XPC error event before bootstrap event");
      }
      return;
    }

    const char* messageName = xpc_dictionary_get_string(aEvent, "message-name");
    if (!messageName) {
      NSLog(@"[%d] No message name specified in XPC message", getpid());
      return;
    }

    if (!strcmp(messageName, "bootstrap")) {
      HandleBootstrapMessage(aEvent);
      // Errors on the XPC channel no longer indicate we should shut down.
      geckoViewStarted = true;
    } else {
      NS_WARNING(nsPrintfCString("Unknown XPC message: %s", messageName).get());
    }
  });

  xpc_connection_activate(aXpcConnection);
}

MOZ_EXPORT __attribute__((used)) void ReportChildProcessJITEnabled(
    int32_t aPid, bool aEnabled) {
  mozilla::widget::ReportChildProcessJITEnabled(aPid, aEnabled);
}

static int ChildProcessInitImpl(int aArgc, char** aArgv) {
  auto bootstrap = mozilla::GetBootstrap();
  if (bootstrap.isErr()) {
    printf_stderr("Couldn't load XPCOM.\n");
    return 255;
  }
  // Check for the absolute minimum number of args we need to move
  // forward here. We expect the last arg to be the child process type,
  // and the second-last argument to be the gecko child id.
  if (aArgc < 2) {
    return 3;
  }

  // Set the process type. We don't remove the arg here as that will be
  // done later in common code.
  mozilla::SetGeckoProcessType(aArgv[aArgc - 1]);

  XREChildData childData;

  mozilla::SetGeckoChildID(aArgv[aArgc - 2]);

#if defined(MOZ_MEMORY)
  jemalloc_reset_small_alloc_randomization(
      /* aRandomizeSmall */ !XRE_IsContentProcess());
#endif

  // REYNARD: Probe the child process directly for writable-to-executable page
  // transitions before SpiderMonkey initializes executable memory. This keeps
  // JIT gating independent from the NSExtension bootstrap path.
  const bool isContentProcess = XRE_IsContentProcess();
  fprintf(stderr, "REYNARD_DEBUG: Child JIT gate pid=%d, content=%d\n",
          getpid(), isContentProcess);
  fflush(stderr);
  if (isContentProcess) {
    int jitErrno = 0;
    if (WaitForExecutableJITReady(&jitErrno)) {
      fprintf(stderr,
              "REYNARD_DEBUG: Child executable JIT ready, pid=%d\n",
              getpid());
      fflush(stderr);
    } else {
      fprintf(stderr,
              "REYNARD_DEBUG: JIT enablement verification failed, pid=%d, errno=%d\n",
              getpid(), jitErrno);
      fprintf(stderr,
              "REYNARD_DEBUG: DisableJitBackend from IOSBootstrap executable JIT preflight failure, pid=%d\n",
              getpid());
      fflush(stderr);
      JS::DisableJitBackend();
    }
  } else {
    fprintf(stderr,
            "REYNARD_DEBUG: DisableJitBackend from IOSBootstrap non-content child process, pid=%d\n",
            getpid());
    fflush(stderr);
    JS::DisableJitBackend();
  }

  nsresult rv =
      bootstrap.inspect()->XRE_InitChildProcess(aArgc - 2, aArgv, &childData);

  return NS_FAILED(rv);
}

void HandleBootstrapMessage(xpc_object_t aEvent) {
  // Set up stdout and stderr if they were provided.
  int fd = xpc_dictionary_dup_fd(aEvent, "stdout");
  if (fd != -1) {
    MOZ_ASSERT(fd != STDOUT_FILENO);
    dup2(fd, STDOUT_FILENO);
    close(fd);
  }
  fd = xpc_dictionary_dup_fd(aEvent, "stderr");
  if (fd != -1) {
    MOZ_ASSERT(fd != STDERR_FILENO);
    dup2(fd, STDERR_FILENO);
    close(fd);
  }

  fd = xpc_dictionary_dup_fd(aEvent, "jit-ready-fd");
  if (fd != -1) {
    gExecutableJITReadyFd = fd;
  }

  // Immediately send a reply with our pid
  auto reply = mozilla::AdoptDarwinObject(xpc_dictionary_create_reply(aEvent));
  xpc_dictionary_set_int64(reply.get(), "pid", getpid());
  xpc_connection_send_message(xpc_dictionary_get_remote_connection(aEvent),
                              reply.get());

  // Load any environment variable overrides set by the parent process.
  xpc_object_t newEnviron = xpc_dictionary_get_dictionary(aEvent, "environ");
  xpc_dictionary_apply(newEnviron, [](const char* key, xpc_object_t value) {
    setenv(key, xpc_string_get_string_ptr(value), 1);
    return true;
  });

  xpc_object_t fds = xpc_dictionary_get_array(aEvent, "fds");
  if (!fds) {
    MOZ_CRASH("fds array not specified");
    return;
  }

  size_t num_fds = xpc_array_get_count(fds);
  std::vector<mozilla::UniqueFileHandle> files;
  files.reserve(num_fds);
  for (size_t i = 0; i < num_fds; ++i) {
    files.emplace_back(xpc_array_dup_fd(fds, i));
  }

  mozilla::geckoargs::SetPassedFileHandles(std::move(files));

  xpc_object_t sendRightsArray = xpc_dictionary_get_array(aEvent, "sendRights");
  if (!sendRightsArray) {
    MOZ_CRASH("sendRights array not specified");
    return;
  }

  size_t num_rights = xpc_array_get_count(sendRightsArray);
  std::vector<mozilla::UniqueMachSendRight> sendRights;
  sendRights.reserve(num_rights);
  for (size_t i = 0; i < num_rights; ++i) {
    // NOTE: As iOS doesn't expose an xpc_array_set_mach_send method, the
    // port is wrapped with a single-key dictionary.
    xpc_object_t sendRightWrapper =
        xpc_array_get_dictionary(sendRightsArray, i);
    if (!sendRightWrapper) {
      MOZ_CRASH("invalid sendRights array");
      continue;
    }
    sendRights.emplace_back(
        xpc_dictionary_copy_mach_send(sendRightWrapper, "port"));
  }

  mozilla::geckoargs::SetPassedMachSendRights(std::move(sendRights));

  // Populate a new argv array with our argument list from IPC.
  xpc_object_t args = xpc_dictionary_get_array(aEvent, "argv");
  if (!args) {
    MOZ_CRASH("argv array not specified");
    return;
  }

  int argc = static_cast<int>(xpc_array_get_count(args));
  char** argv = new char*[argc + 1];
  for (int i = 0; i < argc; ++i) {
    argv[i] = strdup(xpc_array_get_string(args, i));
  }
  argv[argc] = nullptr;

  /* dispatch_async(dispatch_get_main_queue(),
                 [argc, argv] { _exit(ChildProcessInitImpl(argc, argv)); });
  */

  // REYNARD: Run Gecko child bootstrap off the NSExtension main queue so
  // host lifecycle notifications can still be serviced synchronously.
  dispatch_async(dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0),
                 [argc, argv] { _exit(ChildProcessInitImpl(argc, argv)); });
}
