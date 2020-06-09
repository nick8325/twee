#include <sys/prctl.h>
#include <sys/signal.h>
#include <stdlib.h>
#include <unistd.h>

void link_to_parent(pid_t parent) {
    prctl(PR_SET_PDEATHSIG, SIGTERM);

    pid_t ppid = getppid();
    if (ppid != parent)
        exit(1);
}
