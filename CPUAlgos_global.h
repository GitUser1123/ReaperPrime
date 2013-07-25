#ifndef CPUALGOS_GLOBAL_H
#define CPUALGOS_GLOBAL_H

#include "gmp.h"

#include "mpz_w.h"

vector<uchar> XPM_create_auxdata(mpz_t* bnChainOrigin);

void CPU_Got_share(Reap_CPU_param* state, Work& tempwork,vector<uchar>& auxdata);

static inline
void set_mpz_to_hash(mpz_t *hash, const uint8_t *hashb)
{
	mpz_import(*hash, 8, -1, 4, -1, 0, hashb);
}

extern ullint cpu_shares_hwinvalid;
extern ullint cpu_shares_hwvalid;

extern Work current_work;
extern pthread_mutex_t current_work_mutex;

#endif