#include "Global.h"
#include "Config.h"

//#include <stdbool.h>
#include <cstddef>
#include <cstdint>
#include <cstdio>
//#include <sys/time.h>

#include "gmp.h"

#ifdef WIN32
#include "windows.h"
#endif

struct bfgtls_data {
	char *bfg_strerror_result;
	size_t bfg_strerror_resultsz;
#ifdef WIN32
	LPSTR bfg_strerror_socketresult;
#endif
	void *prime_longterms;
};


struct work {
	unsigned char	data[128];
	unsigned char	midstate[32];
	unsigned char	target[32];
	unsigned char	hash[32];
	
	uint8_t *sig;
	size_t sigsz;

	uint64_t	share_diff;

	int		rolls;

//	dev_blk_ctx	blk;

	struct thr_info	*thr;
	int		thr_id;
	struct pool	*pool;
//	struct timeval	tv_staged;

	bool		mined;
	bool		clone;
	bool		cloned;
	int		rolltime;
	bool		longpoll;
	bool		stale;
	bool		mandatory;
	bool		block;
	bool		queued;

	bool		stratum;
	char 		*job_id;
//	bytes_t		nonce2;
	double		sdiff;
	char		*nonce1;

	unsigned char	work_restart_id;
	int		id;
//	UT_hash_handle hh;
	
	double		work_difficulty;

	// Allow devices to identify work if multiple sub-devices
	// DEPRECATED: New code should be using multiple processors instead
	unsigned char	subid;

//	blktemplate_t	*tmpl;
	int		*tmpl_refcount;
	unsigned int	dataid;
	bool		do_foreign_submit;

//	struct timeval	tv_getwork;
//	struct timeval	tv_getwork_reply;
//	struct timeval	tv_cloned;
//	struct timeval	tv_work_start;
//	struct timeval	tv_work_found;
	char		getwork_mode;

	/* Used to queue shares in submit_waiting */
	struct work *prev;
	struct work *next;
};


void cgtime(struct timeval *tv)
{
/*
#ifdef WIN32
	timeBeginPeriod(1);
#endif
	gettimeofday(tv, NULL);
#ifdef WIN32
	timeEndPeriod(1);
#endif
*/
}

//#include "compat.h"
//#include "miner.h"

#define PRIpreprv "s"

#define nMaxSieveSize 1000000u
#define nPrimeTableLimit nMaxSieveSize
#define nPrimorialTableLimit 100000u

#define PRIME_COUNT 78498
#define PRIMORIAL_COUNT 9592

static
unsigned vPrimes[PRIME_COUNT];
mpz_t bnTwoInverses[PRIME_COUNT];
mpz_t vPrimorials[PRIMORIAL_COUNT];

struct prime_longterms {
	unsigned int nPrimorialHashFactor;
	int64_t nTimeExpected;   // time expected to prime chain (micro-second)
	int64_t nTimeExpectedPrev; // time expected to prime chain last time
	bool fIncrementPrimorial; // increase or decrease primorial factor
	unsigned current_prime;
	int64_t nHPSTimerStart;
	int64_t nLogTime;
	int64_t nPrimeCounter;
	int64_t nTestCounter;
#ifdef USE_WEAVE_CHEMISIST
	unsigned timeouts;
	unsigned completed;
	int sieveBuildTime;
#endif
};

static struct prime_longterms *get_prime_longterms();

static
int64_t GetTimeMicros()
{
//	struct timeval tv;
//	cgtime(&tv);
//	return ((int64_t)tv.tv_sec * 1000000) + tv.tv_usec;

	return (int64_t)(ticker())*1000;
}

static
int64_t GetTimeMillis()
{
	return GetTimeMicros() / 1000;
}

static
int64_t GetTime()
{
	return GetTimeMicros() / 1000000;
}

static
bool error(const char *fmt, ...)
{
	puts(fmt);  // FIXME
	return false;
}

mpz_t bnTwo;

void GeneratePrimeTable()
{
	mpz_init_set_ui(bnTwo, 2);
	
	
	mpz_t bnOne;
	mpz_init_set_ui(bnOne, 1);
	
	mpz_t *bnLastPrimorial = &bnOne;
	unsigned i = 0;
	// Generate prime table using sieve of Eratosthenes
	bool vfComposite[nPrimeTableLimit] = {false};
	for (unsigned int nFactor = 2; nFactor * nFactor < nPrimeTableLimit; nFactor++)
	{
	    if (vfComposite[nFactor])
	        continue;
	    for (unsigned int nComposite = nFactor * nFactor; nComposite < nPrimeTableLimit; nComposite += nFactor)
	        vfComposite[nComposite] = true;
	}
	for (unsigned int n = 2; n < nPrimeTableLimit; n++)
		if (!vfComposite[n])
		{
			vPrimes[i] = n;
			
			if (n > 2)
			{
				// bnOne isn't 1 here, which is okay since it is no longer needed as 1 after prime 2
				mpz_init(bnTwoInverses[i]);
				mpz_set_ui(bnOne, n);
				if (!mpz_invert(bnTwoInverses[i], bnTwo, bnOne))
				{
					printf("mpz_invert of 2 failed for prime %u", n);
					throw string("Fataali Erryyri");
				}
			}
			
			if (n < nPrimorialTableLimit)
			{
				mpz_init(vPrimorials[i]);
				mpz_mul_ui(vPrimorials[i], *bnLastPrimorial, n);
				bnLastPrimorial = &vPrimorials[i];
			}
			
			++i;
		}
	mpz_clear(bnOne);
	//applog(LOG_DEBUG, "GeneratePrimeTable() : prime table [1, %d] generated with %lu primes", nPrimeTableLimit, (unsigned long)i);
	printf("GeneratePrimeTable() : prime table [1, %d] generated with %lu primes", nPrimeTableLimit, (unsigned long)i);
}

#define nFractionalBits 24
#define TARGET_FRACTIONAL_MASK ((1u << nFractionalBits) - 1)
#define TARGET_LENGTH_MASK (~TARGET_FRACTIONAL_MASK)

// Check Fermat probable primality test (2-PRP): 2 ** (n-1) = 1 (mod n)
// true: n is probable prime
// false: n is composite; set fractional length in the nLength output
static
bool FermatProbablePrimalityTest(mpz_t *n, unsigned int *pnLength)
{
	mpz_t a, e, r;
	mpz_init_set_ui(a, 2); // base; Fermat witness
	mpz_init(e);
	mpz_sub_ui(e, *n, 1);
	mpz_init(r);
	
	mpz_powm(r, a, e, *n); // r = (2**(n-1))%n
	mpz_clear(a);
	mpz_clear(e);
	if (!mpz_cmp_ui(r, 1)) //if r is 1, this is a witness!
	{
		mpz_clear(r);
		return true;
	}
	
	// Failed Fermat test, calculate fractional length
	// nFractionalLength = ( (n-r) << nFractionalBits ) / n
	mpz_sub(r, *n, r);
	mpz_mul_2exp(r, r, nFractionalBits);
	mpz_fdiv_q(r, r, *n);
	unsigned int nFractionalLength = mpz_get_ui(r);
	mpz_clear(r);
	
	if (nFractionalLength >= (1 << nFractionalBits))
		return error("FermatProbablePrimalityTest() : fractional assert");
	*pnLength = (*pnLength & TARGET_LENGTH_MASK) | nFractionalLength;
	return false;
}

static
unsigned int TargetGetLength(unsigned int nBits)
{
	return ((nBits & TARGET_LENGTH_MASK) >> nFractionalBits);
}

static
void TargetIncrementLength(unsigned int *pnBits)
{
    *pnBits += (1 << nFractionalBits);
}

// Test probable primality of n = 2p +/- 1 based on Euler, Lagrange and Lifchitz
// fSophieGermain:
//   true:  n = 2p+1, p prime, aka Cunningham Chain of first kind
//   false: n = 2p-1, p prime, aka Cunningham Chain of second kind
// Return values
//   true: n is probable prime
//   false: n is composite; set fractional length in the nLength output
static
bool EulerLagrangeLifchitzPrimalityTest(mpz_t *n, bool fSophieGermain, unsigned int *pnLength)
{
	mpz_t a, e, r;
	mpz_init_set_ui(a, 2);
	mpz_init(e);
	mpz_sub_ui(e, *n, 1);
	mpz_fdiv_q_2exp(e, e, 1);
	mpz_init(r);
	
	mpz_powm(r, a, e, *n);
	mpz_clear(a);
	mpz_clear(e);
	unsigned nMod8 = mpz_fdiv_ui(*n, 8);
	bool fPassedTest = false;
	if (fSophieGermain && (nMod8 == 7)) // Euler & Lagrange
		fPassedTest = !mpz_cmp_ui(r, 1);
	else if (nMod8 == (fSophieGermain ? 3 : 5)) // Lifchitz
	{
		mpz_t mp;
		mpz_init_set_ui(mp, 1);
		mpz_add(mp, r, mp);
		fPassedTest = !mpz_cmp(mp, *n);
		mpz_clear(mp);
	}
	else if ((!fSophieGermain) && (nMod8 == 1)) // LifChitz
		fPassedTest = !mpz_cmp_ui(r, 1);
	else
	{
		mpz_clear(r);
		cout << "ELLP Test: invalud n%%8 = " << nMod8 << ", " << (fSophieGermain?"First kind","Second kind") << endl;
		return;
		//return error("EulerLagrangeLifchitzPrimalityTest() : invalid n %% 8 = %d, %s", nMod8, (fSophieGermain? "first kind" : "second kind"));
	}

	if (fPassedTest)
	{
		mpz_clear(r);
		return true;
	}
	// Failed test, calculate fractional length
	
	// derive Fermat test remainder
	mpz_mul(r, r, r);
	mpz_fdiv_r(r, r, *n);
	
	// nFractionalLength = ( (n-r) << nFractionalBits ) / n
	mpz_sub(r, *n, r);
	mpz_mul_2exp(r, r, nFractionalBits);
	mpz_fdiv_q(r, r, *n);
	unsigned int nFractionalLength = mpz_get_ui(r);
	mpz_clear(r);
	
	if (nFractionalLength >= (1 << nFractionalBits))
	{
		cout << "EulerLagrangeLifchitzPrimalityTest() : fractional assert" << endl;
		return;
		//return error("EulerLagrangeLifchitzPrimalityTest() : fractional assert");
	}
	*pnLength = (*pnLength & TARGET_LENGTH_MASK) | nFractionalLength;
	return false;
}

// Test Probable Cunningham Chain for: n
// fSophieGermain:
//   true - Test for Cunningham Chain of first kind (n, 2n+1, 4n+3, ...)
//   false - Test for Cunningham Chain of second kind (n, 2n-1, 4n-3, ...)
// Return value:
//   true - Probable Cunningham Chain found (length at least 2)
//   false - Not Cunningham Chain
static
bool ProbableCunninghamChainTest(mpz_t *n, bool fSophieGermain, bool fFermatTest, unsigned int *pnProbableChainLength)
{
#ifdef SUPERDEBUG
	printf("ProbableCunninghamChainTest(");
	mpz_out_str(stdout, 0x10, *n);
	printf(", %d, %d, %u)\n", (int)fSophieGermain, (int)fFermatTest, *pnProbableChainLength);
#endif
	
	*pnProbableChainLength = 0;
	mpz_t N;
	mpz_init_set(N, *n);
	
	// Fermat test for n first
	if (!FermatProbablePrimalityTest(&N, pnProbableChainLength))
	{
		mpz_clear(N);
		return false;
	}
#ifdef SUPERDEBUG
	printf("N=");
	mpz_out_str(stdout, 0x10, N);
	printf("\n");
#endif

	// Euler-Lagrange-Lifchitz test for the following numbers in chain
	while (true)
	{
		TargetIncrementLength(pnProbableChainLength);
		mpz_add(N, N, N);
		if (fSophieGermain)
			mpz_add_ui(N, N, 1);
		else
			mpz_sub_ui(N, N, 1);
		if (fFermatTest)
		{
			if (!FermatProbablePrimalityTest(&N, pnProbableChainLength))
				break;
		}
		else
		{
#ifdef SUPERDEBUG
			if (!fSophieGermain)
			{
				printf("EulerLagrangeLifchitzPrimalityTest(");
				mpz_out_str(stdout, 0x10, N);
				printf(", 1, %d)\n", *pnProbableChainLength);
			}
#endif
			if (!EulerLagrangeLifchitzPrimalityTest(&N, fSophieGermain, pnProbableChainLength))
				break;
		}
	}
	mpz_clear(N);

#ifdef SUPERDEBUG
	printf("PCCT => %u (%u)\n", TargetGetLength(*pnProbableChainLength), *pnProbableChainLength);
#endif
	return (TargetGetLength(*pnProbableChainLength) >= 2);
}

static
unsigned int TargetFromInt(unsigned int nLength)
{
    return (nLength << nFractionalBits);
}

// Test probable prime chain for: nOrigin
// Return value:
//   true - Probable prime chain found (one of nChainLength meeting target)
//   false - prime chain too short (none of nChainLength meeting target)
static
bool ProbablePrimeChainTest(mpz_t *bnPrimeChainOrigin, unsigned int nBits, bool fFermatTest, unsigned int *pnChainLengthCunningham1, unsigned int *pnChainLengthCunningham2, unsigned int *pnChainLengthBiTwin)
{
	*pnChainLengthCunningham1 = 0;
	*pnChainLengthCunningham2 = 0;
	*pnChainLengthBiTwin = 0;
	
	mpz_t mp;
	mpz_init(mp);
	
	// Test for Cunningham Chain of first kind
	mpz_sub_ui(mp, *bnPrimeChainOrigin, 1);
	ProbableCunninghamChainTest(&mp, true, fFermatTest, pnChainLengthCunningham1);
	// Test for Cunningham Chain of second kind
	mpz_add_ui(mp, *bnPrimeChainOrigin, 1);
	ProbableCunninghamChainTest(&mp, false, fFermatTest, pnChainLengthCunningham2);
	mpz_clear(mp);
	// Figure out BiTwin Chain length
	// BiTwin Chain allows a single prime at the end for odd length chain
	*pnChainLengthBiTwin = (TargetGetLength(*pnChainLengthCunningham1) > TargetGetLength(*pnChainLengthCunningham2)) ? (*pnChainLengthCunningham2 + TargetFromInt(TargetGetLength(*pnChainLengthCunningham2)+1)) : (*pnChainLengthCunningham1 + TargetFromInt(TargetGetLength(*pnChainLengthCunningham1)));
	
	return (*pnChainLengthCunningham1 >= nBits || *pnChainLengthCunningham2 >= nBits || *pnChainLengthBiTwin >= nBits);
}

struct SieveOfEratosthenes {
	bool valid;
	
	unsigned int nSieveSize; // size of the sieve
	unsigned int nBits; // target of the prime chain to search for
	mpz_t hashBlockHeader; // block header hash
	mpz_t bnFixedFactor; // fixed factor to derive the chain

	// bitmaps of the sieve, index represents the variable part of multiplier
	bool vfCompositeCunningham1[1000000];
	bool vfCompositeCunningham2[1000000];
	bool vfCompositeBiTwin[1000000];

	unsigned int nPrimeSeq; // prime sequence number currently being processed
	unsigned int nCandidateMultiplier; // current candidate for power test
};

static
void psieve_reset(struct SieveOfEratosthenes *psieve)
{
	mpz_clear(psieve->hashBlockHeader);
	mpz_clear(psieve->bnFixedFactor);
	psieve->valid = false;
}

static
void psieve_init(struct SieveOfEratosthenes *psieve, unsigned nSieveSize, unsigned nBits, mpz_t *hashBlockHeader, mpz_t *bnFixedMultiplier)
{
	if (psieve->valid)
		cout << "SIEVE IS VALID, WTF" << endl;
	//assert(!psieve->valid);
	/* *psieve = (struct SieveOfEratosthenes){
		.valid = true,
		.nSieveSize = nSieveSize,
		.nBits = nBits,
	};*/
	*psieve = SieveOfEratosthenes();
	psieve->valid = true;
	psieve->nSieveSize = nSieveSize;
	psieve->nBits = nBits;
	
	mpz_init_set(psieve->hashBlockHeader, *hashBlockHeader);
	mpz_init(psieve->bnFixedFactor);
	mpz_mul(psieve->bnFixedFactor, *bnFixedMultiplier, *hashBlockHeader);
}

#ifdef USE_WEAVE_CHEMISIST

#define TESTING_FREQUENCY 1000

static
void Weave_Chemisist(struct thr_info *thr, struct SieveOfEratosthenes *psieve) {
	struct prime_longterms *pl = get_prime_longterms();
	
	int64_t nStart = GetTimeMicros(), nCurrent = GetTimeMicros();
	mpz_t bnFixedInverse, p;
	mpz_init(bnFixedInverse);
	mpz_init(p);
	unsigned int nChainLength = TargetGetLength(psieve->nBits);
	unsigned int nChainLength2 = 2*nChainLength;
	unsigned int nSolvedMultiplier, nVariableMultiplier, nBiTwinSeq, uP;
	unsigned int nPrimeSeqMax;
	mpz_t *pbnTwoInverse;
	if(vPrimes[PRIME_COUNT-1] < psieve->nSieveSize) {
		nPrimeSeqMax = PRIME_COUNT;
	} else {
		for(nPrimeSeqMax = 0; nPrimeSeqMax < PRIME_COUNT && vPrimes[nPrimeSeqMax] < psieve->nSieveSize; nPrimeSeqMax++) ;
	}

	// create no new variables during the loop to eliminate all malloc() operations
	for(psieve->nPrimeSeq = 0; psieve->nPrimeSeq < nPrimeSeqMax; psieve->nPrimeSeq++) {
		uP = vPrimes[psieve->nPrimeSeq];  // aka nPrime
		mpz_set_ui(p, uP);

		if (mpz_fdiv_ui(psieve->bnFixedFactor, uP) == 0)
		{
			// Nothing in the sieve is divisible by this prime
			continue;
		}
		// Find the modulo inverse of fixed factor
		if (!mpz_invert(bnFixedInverse, psieve->bnFixedFactor, p))
		{
			// TODO: mpz_clear
			error("CSieveOfEratosthenes::Weave(): BN_mod_inverse of fixed factor failed for prime #%u=%u", psieve->nPrimeSeq, uP);
			return;
		}
		pbnTwoInverse = &bnTwoInverses[psieve->nPrimeSeq];
		// calling the GetTimeMicros() method and the additional boolean testing ends up taking a while, so the speed can be increased by just calculating it every so often.
		if(psieve->nPrimeSeq % TESTING_FREQUENCY == 0)
		{
			nCurrent = GetTimeMicros() - nStart;
			if(nCurrent > (pl->sieveBuildTime))
				return;
		}

		for (nBiTwinSeq = 0; nBiTwinSeq < nChainLength; nBiTwinSeq++)
		{
			if((nBiTwinSeq & 1u) == 0)
			{
				mpz_mul_ui(p, bnFixedInverse, uP + 1);
				nSolvedMultiplier = mpz_fdiv_ui(p, uP);
				for (nVariableMultiplier = nSolvedMultiplier; nVariableMultiplier < psieve->nSieveSize; nVariableMultiplier += uP)
					psieve->vfCompositeCunningham1[nVariableMultiplier] = true;
			}
			else
			{
				mpz_mul_ui(p, bnFixedInverse, uP - 1);
				nSolvedMultiplier = mpz_fdiv_ui(p, uP);
				mpz_mul(bnFixedInverse, bnFixedInverse, *pbnTwoInverse); // for next number in chain
				for (nVariableMultiplier = nSolvedMultiplier; nVariableMultiplier < psieve->nSieveSize; nVariableMultiplier += uP)
					psieve->vfCompositeCunningham2[nVariableMultiplier] = true;
			}
			for (nVariableMultiplier = nSolvedMultiplier; nVariableMultiplier < psieve->nSieveSize; nVariableMultiplier += uP)
				psieve->vfCompositeBiTwin[nVariableMultiplier] = true;
		}
		// continue loop without the composite_bi_twin
		for (; nBiTwinSeq < nChainLength2; nBiTwinSeq++)
		{
			if((nBiTwinSeq & 1u) == 0)
			{
				mpz_mul_ui(p, bnFixedInverse, uP + 1);
				nSolvedMultiplier = mpz_fdiv_ui(p, uP);
				for (nVariableMultiplier = nSolvedMultiplier; nVariableMultiplier < psieve->nSieveSize; nVariableMultiplier += uP)
					psieve->vfCompositeCunningham1[nVariableMultiplier] = true;
			}
			else
			{
				mpz_mul_ui(p, bnFixedInverse, uP - 1);
				nSolvedMultiplier = mpz_fdiv_ui(p, uP);
				mpz_mul(bnFixedInverse, bnFixedInverse, *pbnTwoInverse); // for next number in chain
				for (nVariableMultiplier = nSolvedMultiplier; nVariableMultiplier < psieve->nSieveSize; nVariableMultiplier += uP)
					psieve->vfCompositeCunningham2[nVariableMultiplier] = true;
			}
		}
	}
}

#else

// Weave sieve for the next prime in table
// Return values:
//   True  - weaved another prime; nComposite - number of composites removed
//   False - sieve already completed
static
bool psieve_Weave(struct SieveOfEratosthenes *psieve)
{
	unsigned nPrime = vPrimes[psieve->nPrimeSeq];
	if (psieve->nPrimeSeq >= PRIME_COUNT || nPrime >= psieve->nSieveSize)
		return false;  // sieve has been completed
	if (mpz_fdiv_ui(psieve->bnFixedFactor, nPrime) == 0)
	{
		// Nothing in the sieve is divisible by this prime
		++psieve->nPrimeSeq;
		return true;
	}
	// Find the modulo inverse of fixed factor
	mpz_t bnFixedInverse, p;
	mpz_init(bnFixedInverse);
	mpz_init_set_ui(p, nPrime);
	if (!mpz_invert(bnFixedInverse, psieve->bnFixedFactor, p))
	{
		mpz_clear(p);
		mpz_clear(bnFixedInverse);
		return error("CSieveOfEratosthenes::Weave(): BN_mod_inverse of fixed factor failed for prime #%u=%u", psieve->nPrimeSeq, nPrime);
	}
	mpz_t *pbnTwoInverse = &bnTwoInverses[psieve->nPrimeSeq];

	// Weave the sieve for the prime
	unsigned int nChainLength = TargetGetLength(psieve->nBits);
	for (unsigned int nBiTwinSeq = 0; nBiTwinSeq < 2 * nChainLength; nBiTwinSeq++)
	{
		bool b = nBiTwinSeq & 1;
		// Find the first number that's divisible by this prime
		int nDelta = (b ? 1 : -1);
		mpz_mul_ui(p, bnFixedInverse, nPrime - nDelta);
		unsigned int nSolvedMultiplier = mpz_fdiv_ui(p, nPrime);
		
		if (b)
			mpz_mul(bnFixedInverse, bnFixedInverse, *pbnTwoInverse); // for next number in chain

		if (nBiTwinSeq < nChainLength)
			for (unsigned int nVariableMultiplier = nSolvedMultiplier; nVariableMultiplier < psieve->nSieveSize; nVariableMultiplier += nPrime)
				psieve->vfCompositeBiTwin[nVariableMultiplier] = true;
		if (!b)
		{
			for (unsigned int nVariableMultiplier = nSolvedMultiplier; nVariableMultiplier < psieve->nSieveSize; nVariableMultiplier += nPrime)
				psieve->vfCompositeCunningham1[nVariableMultiplier] = true;
		}
		else
			for (unsigned int nVariableMultiplier = nSolvedMultiplier; nVariableMultiplier < psieve->nSieveSize; nVariableMultiplier += nPrime)
				psieve->vfCompositeCunningham2[nVariableMultiplier] = true;
	}
	mpz_clear(p);
	mpz_clear(bnFixedInverse);
	++psieve->nPrimeSeq;
	return true;
}

#endif

static
bool psieve_GetNextCandidateMultiplier(struct SieveOfEratosthenes *psieve, unsigned int *pnVariableMultiplier)
{
	while (true)
	{
		psieve->nCandidateMultiplier++;
		if (psieve->nCandidateMultiplier >= psieve->nSieveSize)
		{
			psieve->nCandidateMultiplier = 0;
			return false;
		}
		if (!psieve->vfCompositeCunningham1[psieve->nCandidateMultiplier] ||
			!psieve->vfCompositeCunningham2[psieve->nCandidateMultiplier] ||
			!psieve->vfCompositeBiTwin[psieve->nCandidateMultiplier])
			{
				*pnVariableMultiplier = psieve->nCandidateMultiplier;
				return true;
			}
	}
}

// Get total number of candidates for power test
static
unsigned int psieve_GetCandidateCount(struct SieveOfEratosthenes *psieve)
{
	unsigned int nCandidates = 0;
	for (unsigned int nMultiplier = 0; nMultiplier < psieve->nSieveSize; nMultiplier++)
	{
		if (!psieve->vfCompositeCunningham1[nMultiplier] || !psieve->vfCompositeCunningham2[nMultiplier] || !psieve->vfCompositeBiTwin[nMultiplier])
		nCandidates++;
	}
	return nCandidates;
}

// Get progress percentage of the sieve
static
unsigned psieve_GetProgressPercentage(struct SieveOfEratosthenes *psieve)
{
	unsigned rv;
	if (psieve->nPrimeSeq >= PRIME_COUNT)
		rv = nPrimeTableLimit;
	else
		rv = vPrimes[psieve->nPrimeSeq];
	rv = rv * 100 / psieve->nSieveSize;
	if (rv > 100)
		rv = 100;
	return rv;
}

// Mine probable prime chain of form: n = h * p# +/- 1
bool MineProbablePrimeChain(struct thr_info *thr, struct SieveOfEratosthenes *psieve, const uint8_t *header, mpz_t *hash, mpz_t *bnFixedMultiplier, bool *pfNewBlock, unsigned *pnTriedMultiplier, unsigned *pnProbableChainLength, unsigned *pnTests, unsigned *pnPrimesHit, struct work *work)
{
	//const char *proc_repr = thr->cgpu->proc_repr;
	const char* proc_repr = "TESTPROCESS :D";
#ifdef USE_WEAVE_CHEMISIST
	struct prime_longterms *pl = get_prime_longterms();
#endif
	const uint32_t *pnbits = (const uint32_t*)&header[72];
	*pnProbableChainLength = 0;
	*pnTests = 0;
	*pnPrimesHit = 0;

	if (*pfNewBlock && psieve->valid)
	{
	    // Must rebuild the sieve
	    psieve_reset(psieve);
	}
	*pfNewBlock = false;

	int64_t nStart, nCurrent; // microsecond timer
#ifdef USE_WEAVE_CHEMISIST
	int64_t nSearch;
#endif
	if (!psieve->valid)
	{
		// Build sieve
		nStart = GetTimeMicros();
#ifdef SUPERDEBUG
		fprintf(stderr, "psieve_init(?, %u, %08x, ", nMaxSieveSize, *pnbits);
		mpz_out_str(stderr, 0x10, *hash);
		fprintf(stderr, ", ");
		mpz_out_str(stderr, 0x10, *bnFixedMultiplier);
		fprintf(stderr, ")\n");
#endif
		psieve_init(psieve, nMaxSieveSize, *pnbits, hash, bnFixedMultiplier);
#ifdef USE_WEAVE_CHEMISIST
		Weave_Chemisist(thr, psieve);
#else
		while (psieve_Weave(psieve))
#endif
			//FIXME: Readd work restart when thread parameters have been implemented
			//if (unlikely(thr->work_restart))
			//{
			//	applog(LOG_DEBUG, "%"PRIpreprv": MineProbablePrimeChain() : weaved interrupted by work restart", proc_repr);
			//	return false;
			//}
 		//applog(LOG_DEBUG, "%"PRIpreprv": MineProbablePrimeChain() : new sieve (%u/%u@%u%%) ready in %uus", proc_repr, psieve_GetCandidateCount(psieve), nMaxSieveSize, psieve_GetProgressPercentage(psieve), (unsigned int) (GetTimeMicros() - nStart));
		printf("%"PRIpreprv": MineProbablePrimeChain() : new sieve (%u/%u@%u%%) ready in %uus", proc_repr, psieve_GetCandidateCount(psieve), nMaxSieveSize, psieve_GetProgressPercentage(psieve), (unsigned int) (GetTimeMicros() - nStart));
	}

	mpz_t bnChainOrigin;
	mpz_init(bnChainOrigin);

	nStart = GetTimeMicros();
	nCurrent = nStart;

#ifdef USE_WEAVE_CHEMISIST
	while (nCurrent - nStart < pl->sieveBuildTime * 3 && nCurrent >= nStart)
#else
	while (nCurrent - nStart < 10000 && nCurrent >= nStart)
#endif
	{
		//FIXME: Readd work restart when thread parameters have been implemented
		/*if (unlikely(thr->work_restart))
		{
			applog(LOG_DEBUG, "%"PRIpreprv": MineProbablePrimeChain() : interrupted by work restart", proc_repr);
			return false;
		}*/
		++*pnTests;
		if (!psieve_GetNextCandidateMultiplier(psieve, pnTriedMultiplier))
		{
			// power tests completed for the sieve
			psieve_reset(psieve);
			*pfNewBlock = true; // notify caller to change nonce
#ifdef USE_WEAVE_CHEMISIST
			++pl->completed;
			nSearch = GetTimeMicros() - nStart;
			if (nSearch < pl->sieveBuildTime)
				pl->sieveBuildTime *= 0.99;
			else
				pl->sieveBuildTime *= 1.01;
			applog(LOG_DEBUG, "%"PRIpreprv": %u ms (Timers: num power tests completed: %u", proc_repr, (unsigned int) (GetTimeMicros() - nStart)/1000, pl->completed);
#endif
			mpz_clear(bnChainOrigin);
			return false;
		}
#ifdef SUPERDEBUG
		printf("nTriedMultiplier=%d\n", *pnTriedMultiplier=640150);
#endif
		mpz_mul(bnChainOrigin, *hash, *bnFixedMultiplier);
		mpz_mul_ui(bnChainOrigin, bnChainOrigin, *pnTriedMultiplier);
		unsigned int nChainLengthCunningham1 = 0;
		unsigned int nChainLengthCunningham2 = 0;
		unsigned int nChainLengthBiTwin = 0;
#ifdef SUPERDEBUG
		printf("ProbablePrimeChainTest(bnChainOrigin=");
		mpz_out_str(stdout, 0x10, bnChainOrigin);
		printf(", nbits=%08lx, false, %d, %d, %d)\n", (unsigned long)*pnbits, nChainLengthCunningham1, nChainLengthCunningham2, nChainLengthBiTwin);
#endif
		if (ProbablePrimeChainTest(&bnChainOrigin, *pnbits, false, &nChainLengthCunningham1, &nChainLengthCunningham2, &nChainLengthBiTwin))
		{
			// bnChainOrigin is not used again, so recycled here for the result

			// block.bnPrimeChainMultiplier = *bnFixedMultiplier * *pnTriedMultiplier;
			mpz_mul_ui(bnChainOrigin, *bnFixedMultiplier, *pnTriedMultiplier);
			
			size_t exportsz, resultoff;
			uint8_t *export_var = (uint8_t*)mpz_export(NULL, &exportsz, -1, 1, -1, 0, bnChainOrigin);
			//assert(exportsz < 250);  // FIXME: bitcoin varint
			if (exportsz < 250) // luke's FIXME: bitcoin varint
				cout << "EXPORTSZ < 250, wtf do i do now" << endl;
			resultoff = 1;
			if (export_var[0] & 0x80)
				++resultoff;
			uint8_t *result = (uint8_t*)malloc(exportsz + resultoff);
			result[0] = exportsz + resultoff - 1;
			result[1] = '\0';
			memcpy(&result[resultoff], export_var, exportsz);
			if (mpz_sgn(bnChainOrigin) < 0)
				result[1] |= 0x80;
			free(export_var);
			
			work->sig = result;
			work->sigsz = exportsz + resultoff;
			
			//char hex[1 + (work->sigsz * 2)];
			//FIXME: enable signature debug print
			//char* hex = new char[1 + (work->sigsz * 2)];
			//bin2hex(hex, work->sig, work->sigsz);
			//applog(LOG_DEBUG, "%"PRIpreprv": SIGNATURE: %s", proc_repr, hex);
			//delete [] hex;
			
			
// 		    printf("Probable prime chain found for block=%s!!\n  Target: %s\n  Length: (%s %s %s)\n", block.GetHash().GetHex().c_str(),
// 		    TargetToString(nbits).c_str(), TargetToString(nChainLengthCunningham1).c_str(), TargetToString(nChainLengthCunningham2).c_str(), TargetToString(nChainLengthBiTwin).c_str());
			printf("%"PRIpreprv": Probable prime chain found for block", proc_repr);
			*pnProbableChainLength = nChainLengthCunningham1;
			if (*pnProbableChainLength < nChainLengthCunningham2)
				*pnProbableChainLength = nChainLengthCunningham2;
			if (*pnProbableChainLength < nChainLengthBiTwin)
				*pnProbableChainLength = nChainLengthBiTwin;
			mpz_clear(bnChainOrigin);
		    return true;
		}
		*pnProbableChainLength = nChainLengthCunningham1;
		if (*pnProbableChainLength < nChainLengthCunningham2)
			*pnProbableChainLength = nChainLengthCunningham2;
		if (*pnProbableChainLength < nChainLengthBiTwin)
			*pnProbableChainLength = nChainLengthBiTwin;
		if(TargetGetLength(*pnProbableChainLength) >= 1)
		    ++*pnPrimesHit;

		nCurrent = GetTimeMicros();
	}
	mpz_clear(bnChainOrigin);
#ifdef USE_WEAVE_CHEMISIST
	++pl->timeouts;
	pl->sieveBuildTime *= 1.025;
	applog(LOG_DEBUG, "%"PRIpreprv": %u ms (Timers: num total time outs: %u", proc_repr, (unsigned int) (GetTimeMicros() - nStart)/1000, pl->completed);
#endif
	return false; // stop as timed out
}

// Checks that the high bit is set, and low bit is clear (ie, divisible by 2)
static
bool check_ends(const uint8_t *hash)
{
	return (hash[31] & 0x80) && !(hash[0] & 1);
}

static inline
void set_mpz_to_hash(mpz_t *hash, const uint8_t *hashb)
{
	mpz_import(*hash, 8, -1, 4, -1, 0, hashb);
}

static
struct prime_longterms *get_prime_longterms()
{
	//struct bfgtls_data *bfgtls = get_bfgtls();
	struct bfgtls_data *bfgtls = NULL; //FIXME: GET ACTUAL BFGTLS THING
	
	struct prime_longterms *pl = (prime_longterms*)(bfgtls->prime_longterms);
	if ((!pl))
	{
		bfgtls->prime_longterms = (prime_longterms*)malloc(sizeof(*pl));
		pl = (prime_longterms*)bfgtls->prime_longterms;
		*pl = prime_longterms();
		pl->nPrimorialHashFactor = 7;
		pl->fIncrementPrimorial = true;
		pl->current_prime = 3;
		pl->nHPSTimerStart = GetTimeMillis();
#ifdef USE_WEAVE_CHEMISIST
		pl->sieveBuildTime = 400000;
#endif


		/* *pl = (struct prime_longterms){
			.nPrimorialHashFactor = 7,
			.fIncrementPrimorial = true,
			.current_prime = 3,  // index 3 is prime number 7
			.nHPSTimerStart = GetTimeMillis(),
#ifdef USE_WEAVE_CHEMISIST
			.sieveBuildTime = 400000,
#endif
		};*/
	}
	return pl;
}

bool prime(struct thr_info *thr, uint8_t *header, struct work *work)
{
	//const char *proc_repr = thr->cgpu->proc_repr;
	//FIXME: add proper process representation
	const char* proc_repr = "ei lol :D:D";
	struct prime_longterms *pl = get_prime_longterms();
	bool rv = false;
	
	uint32_t *nonce = (uint32_t*)(&header[76]);
	unsigned char hashb[32];
	mpz_t hash, bnPrimeMin;
	
	mpz_init(hash);
	mpz_init_set_ui(bnPrimeMin, 1);
	mpz_mul_2exp(bnPrimeMin, bnPrimeMin, 255);
	
	bool fNewBlock = true;
	unsigned int nTriedMultiplier = 0;

	SieveOfEratosthenes* sieve = new SieveOfEratosthenes;
	sieve->valid = false;

	/*struct SieveOfEratosthenes sieve = {
		.valid = false,
	};*/
	
	const unsigned nHashFactor = 210;
	// a valid header must hash to have the MSB set, and a multiple of nHashFactor
	while (true)
	{
		gen_hash(header, hashb, 80);
		if (check_ends(hashb))
		{
			set_mpz_to_hash(&hash, hashb);
			if (!mpz_fdiv_ui(hash, 105))
				break;
		}
		if ((*nonce == 0xffffffff))
		{
			mpz_clear(hash);
			mpz_clear(bnPrimeMin);
			return false;
		}
		++*nonce;
	}
	/*{
		char hex[9];
		bin2hex(hex, nonce, 4);
		applog(LOG_DEBUG, "%"PRIpreprv": Pass 1 found: %s", proc_repr, hex);
	}*/
	
	// primorial fixed multiplier
	mpz_t bnPrimorial;
	mpz_init(bnPrimorial);
	unsigned int nRoundTests = 0;
	unsigned int nRoundPrimesHit = 0;
	int64_t nPrimeTimerStart = GetTimeMicros();
	if (pl->nTimeExpected > pl->nTimeExpectedPrev)
	    pl->fIncrementPrimorial = !pl->fIncrementPrimorial;
	pl->nTimeExpectedPrev = pl->nTimeExpected;
	// dynamic adjustment of primorial multiplier
	if (pl->fIncrementPrimorial)
	{
		++pl->current_prime;
		if (pl->current_prime >= PRIMORIAL_COUNT)
			quit(1, "primorial increment overflow");
	}
	else if (vPrimes[pl->current_prime] > pl->nPrimorialHashFactor)
	{
		if (!pl->current_prime)
			quit(1, "primorial decrement overflow");
		--pl->current_prime;
	}
	mpz_set(bnPrimorial, vPrimorials[pl->current_prime]);
	
	
	while (true)
	{
		unsigned int nTests = 0;
		unsigned int nPrimesHit = 0;
		
		mpz_t bnMultiplierMin;
		// bnMultiplierMin = bnPrimeMin * nHashFactor / hash + 1
		mpz_init(bnMultiplierMin);
		mpz_mul_ui(bnMultiplierMin, bnPrimeMin, nHashFactor);
		mpz_fdiv_q(bnMultiplierMin, bnMultiplierMin, hash);
		mpz_add_ui(bnMultiplierMin, bnMultiplierMin, 1);
		
		while (mpz_cmp(bnPrimorial, bnMultiplierMin) < 0)
		{
			++pl->current_prime;
			if (pl->current_prime >= PRIMORIAL_COUNT)
				quit(1, "primorial minimum overflow");
			mpz_set(bnPrimorial, vPrimorials[pl->current_prime]);
		}
		mpz_clear(bnMultiplierMin);
		
		mpz_t bnFixedMultiplier;
		mpz_init(bnFixedMultiplier);
	    // bnFixedMultiplier = (bnPrimorial > nHashFactor) ? (bnPrimorial / nHashFactor) : 1
		if (mpz_cmp_ui(bnPrimorial, nHashFactor) > 0)
		{
			mpz_t bnHashFactor;
			mpz_init_set_ui(bnHashFactor, nHashFactor);
			mpz_fdiv_q(bnFixedMultiplier, bnPrimorial, bnHashFactor);
			mpz_clear(bnHashFactor);
		}
		else
			mpz_set_ui(bnFixedMultiplier, 1);
#ifdef SUPERDEBUG
		fprintf(stderr,"bnFixedMultiplier=");
		mpz_out_str(stderr, 0x10, bnFixedMultiplier);
		fprintf(stderr, " nPrimorialMultiplier=%u nTriedMultiplier=%u\n", vPrimes[pl->current_prime], nTriedMultiplier);
#endif
		
		
		// mine for prime chain
		unsigned int nProbableChainLength;
		if (MineProbablePrimeChain(thr, sieve, header, &hash, &bnFixedMultiplier, &fNewBlock, &nTriedMultiplier, &nProbableChainLength, &nTests, &nPrimesHit, work))
		{
// TODO			CheckWork(pblock, *pwalletMain, reservekey);
			mpz_clear(bnFixedMultiplier);
			rv = true;
			break;
		}
		if ((thr->work_restart))
		{
			applog(LOG_DEBUG, "%"PRIpreprv": prime interrupted by work restart", proc_repr);
			break;
		}
		mpz_clear(bnFixedMultiplier);
		nRoundTests += nTests;
		nRoundPrimesHit += nPrimesHit;

	    // Meter primes/sec
	    if (pl->nHPSTimerStart == 0)
	    {
	        pl->nHPSTimerStart = GetTimeMillis();
	        pl->nPrimeCounter = 0;
	        pl->nTestCounter = 0;
	    }
	    else
	    {
	        pl->nPrimeCounter += nPrimesHit;
	        pl->nTestCounter += nTests;
	    }
		
		
		if (GetTimeMillis() - pl->nHPSTimerStart > 60000)
		{
			double dPrimesPerMinute = 60000.0 * pl->nPrimeCounter / (GetTimeMillis() - pl->nHPSTimerStart);
			double dPrimesPerSec = dPrimesPerMinute / 60.0;
			double dTestsPerMinute = 60000.0 * pl->nTestCounter / (GetTimeMillis() - pl->nHPSTimerStart);
			pl->nHPSTimerStart = GetTimeMillis();
			pl->nPrimeCounter = 0;
			pl->nTestCounter = 0;
			if (GetTime() - pl->nLogTime > 60)
			{
				pl->nLogTime = GetTime();
				applog(LOG_NOTICE, "%"PRIpreprv": primemeter %6d test/s %5dpps", proc_repr, (int)(dTestsPerMinute / 60.0), (int)dPrimesPerSec);
			}
		}
		
		
	    // Check for stop or if block needs to be rebuilt
	    // TODO
// 	    boost::this_thread::interruption_point();
// 	    if (vNodes.empty())
// 	        break;
	    if (fNewBlock || thr->work_restart /*|| pblock->nNonce >= 0xffff0000*/)
	        break;
// 	    if (nTransactionsUpdated != nTransactionsUpdatedLast && GetTime() - nStart > 60)
// 	        break;
// 	    if (pindexPrev != pindexBest)
// 	        break;
	}
	mpz_clear(bnPrimorial);

	// Primecoin: estimate time to block
	pl->nTimeExpected = (GetTimeMicros() - nPrimeTimerStart) / max(1u, nRoundTests);
	pl->nTimeExpected = pl->nTimeExpected * max(1u, nRoundTests) / max(1u, nRoundPrimesHit);
//TODO
// 	for (unsigned int n = 1; n < TargetGetLength(pblock->nBits); n++)
// 	     nTimeExpected = nTimeExpected * max(1u, nRoundTests) * 3 / max(1u, nRoundPrimesHit);
	applog(LOG_DEBUG, "%"PRIpreprv": PrimecoinMiner() : Round primorial=%u tests=%u primes=%u expected=%us", proc_repr, vPrimes[pl->current_prime], nRoundTests, nRoundPrimesHit, (unsigned int)(pl->nTimeExpected/1000000));

	mpz_clear(hash);
	mpz_clear(bnPrimeMin);
	delete sieve;

	return rv;
}

bool scanhash_prime(struct thr_info *thr, const unsigned char *pmidstate, unsigned char *pdata, unsigned char *phash1, unsigned char *phash, const unsigned char *ptarget, uint32_t max_nonce, uint32_t *last_nonce, uint32_t nonce)
{
	struct work *work = (struct work *)(&pmidstate[-offsetof(struct work, midstate)]);
	if (work->blk.nonce == 0x10000)
	{
		// HACK: After we found a nonce
next_header:
		*last_nonce = 0xfffffffe;  // HACK: force next header
		return false;
	}
	
	unsigned char header[80];
	swap32yes(header, pdata, 80 / 4);

#ifdef SUPERDEBUG
	char hex[161];
	bin2hex(hex, header, 80);
	applog(LOG_DEBUG, "HEADER: %s", hex);
#endif
	if (!prime(thr, header, work))
		goto next_header;
	swap32yes(&pdata[76], &header[76], 1);
	*last_nonce = 0xffff;  // Trigger HACK above
	return true;
}
