#include <sys/prctl.h>
#include <sys/signal.h>

void link_to_parent(void) {
    prctl(PR_SET_PDEATHSIG, SIGTERM);
}
