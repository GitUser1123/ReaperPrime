#include "Global.h"
#include "CSieveOfEratosthenes.h"
#include "CPUAlgos_global.h"
#include "CPUAlgos.h"

// Get progress percentage of the sieve
unsigned int CSieveOfEratosthenes::GetProgressPercentage()
{
    return std::min(100u, (((nPrimeSeq >= vPrimes.size())? nSieveSize : vPrimes[nPrimeSeq]) * 100 / nSieveSize));
}


void CSieveOfEratosthenes::AddMultiplier(unsigned int *vMultipliers, const unsigned int nSolvedMultiplier)
{
    // Eliminate duplicates
    for (unsigned int i = 0; i < nHalfChainLength; i++)
    {
        unsigned int nStoredMultiplier = vMultipliers[i];
        if (nStoredMultiplier == 0xFFFFFFFF || nStoredMultiplier == nSolvedMultiplier)
        {
            vMultipliers[i] = nSolvedMultiplier;
            break;
        }
    }
}

// Weave sieve for the next prime in table
// Return values:
//   True  - weaved another prime; nComposite - number of composites removed
//   False - sieve already completed
bool CSieveOfEratosthenes::Weave()
{
    // Faster GMP version
    this->nChainLength = TargetGetLength(nBits);
    this->nHalfChainLength = (nChainLength + 1) / 2;

    // Keep all variables local for max performance
    const unsigned int nChainLength = this->nChainLength;
    const unsigned int nHalfChainLength = this->nHalfChainLength;
    //CBlockIndex* pindexPrev = this->pindexPrev;
    unsigned int nSieveSize = this->nSieveSize;
    const unsigned int nTotalPrimes = vPrimes.size();

    // Process only a set percentage of the primes
    // Most composites are still found
    const unsigned int nPrimes = (uint64)nTotalPrimes * nSievePercentage / 100;

    mpz_t mpzFixedFactor; // fixed factor to derive the chain

    unsigned int vCunningham1AMultipliers[nPrimes][nHalfChainLength];
    unsigned int vCunningham1BMultipliers[nPrimes][nHalfChainLength];
    unsigned int vCunningham2AMultipliers[nPrimes][nHalfChainLength];
    unsigned int vCunningham2BMultipliers[nPrimes][nHalfChainLength];

    mpz_init_set(mpzFixedFactor, this->mpzFixedFactor.get_mpz_t());

    memset(vCunningham1AMultipliers, 0xFF, sizeof(vCunningham1AMultipliers));
    memset(vCunningham1BMultipliers, 0xFF, sizeof(vCunningham1BMultipliers));
    memset(vCunningham2AMultipliers, 0xFF, sizeof(vCunningham2AMultipliers));
    memset(vCunningham2BMultipliers, 0xFF, sizeof(vCunningham2BMultipliers));

    // bitsets that can be combined to obtain the final bitset of candidates
    unsigned long *vfCompositeCunningham1A = (unsigned long *)malloc(nCandidatesBytes);
    unsigned long *vfCompositeCunningham1B = (unsigned long *)malloc(nCandidatesBytes);
    unsigned long *vfCompositeCunningham2A = (unsigned long *)malloc(nCandidatesBytes);
    unsigned long *vfCompositeCunningham2B = (unsigned long *)malloc(nCandidatesBytes);

    memset(vfCompositeCunningham1A, 0, nCandidatesBytes);
    memset(vfCompositeCunningham1B, 0, nCandidatesBytes);
    memset(vfCompositeCunningham2A, 0, nCandidatesBytes);
    memset(vfCompositeCunningham2B, 0, nCandidatesBytes);

    unsigned long *vfCandidates = this->vfCandidates;

    for (unsigned int nPrimeSeq = 1; nPrimeSeq < nPrimes; nPrimeSeq++)
    {
		//if (tempwork.time != current_work.time)
		//	break;
        unsigned int nPrime = vPrimes[nPrimeSeq];
        unsigned int nFixedFactorMod = mpz_tdiv_ui(mpzFixedFactor, nPrime);
        if (nFixedFactorMod == 0)
        {
            // Nothing in the sieve is divisible by this prime
            continue;
        }
        // Find the modulo inverse of fixed factor
        unsigned int nFixedInverse = int_invert(nFixedFactorMod, nPrime);
        if (!nFixedInverse)
		{
			cout << "CSieveOfEratosthenes::Weave(): int_invert of fixed factor failed for prime #" << nPrimeSeq << "=" << vPrimes[nPrimeSeq] << endl;
			return false;
            //return error("CSieveOfEratosthenes::Weave(): int_invert of fixed factor failed for prime #%u=%u", nPrimeSeq, vPrimes[nPrimeSeq]);
		}
        unsigned int nTwoInverse = vTwoInverses[nPrimeSeq];

        // Weave the sieve for the prime
        for (unsigned int nBiTwinSeq = 0; nBiTwinSeq < 2 * nChainLength; nBiTwinSeq++)
        {
            // Find the first number that's divisible by this prime
            int nDelta = ((nBiTwinSeq % 2 == 0)? (-1) : 1);
            unsigned int nSolvedMultiplier = (uint64)nFixedInverse * (nPrime - nDelta) % nPrime;
            if (nBiTwinSeq % 2 == 1)
                nFixedInverse = (uint64)nFixedInverse * nTwoInverse % nPrime;

            if (nBiTwinSeq < nChainLength)
            {
                if (((nBiTwinSeq & 1u) == 0))
                    AddMultiplier(vCunningham1AMultipliers[nPrimeSeq], nSolvedMultiplier);
                else
                    AddMultiplier(vCunningham2AMultipliers[nPrimeSeq], nSolvedMultiplier);
            } else {
                if (((nBiTwinSeq & 1u) == 0))
                    AddMultiplier(vCunningham1BMultipliers[nPrimeSeq], nSolvedMultiplier);
                else
                    AddMultiplier(vCunningham2BMultipliers[nPrimeSeq], nSolvedMultiplier);
            }
        }
    }

    // Number of elements that are likely to fit in L1 cache
    const unsigned int nL1CacheElements = 200000;
    const unsigned int nArrayRounds = (nSieveSize + nL1CacheElements - 1) / nL1CacheElements;

    // Loop over each array one at a time for optimal L1 cache performance
    for (unsigned int j = 0; j < nArrayRounds; j++)
    {
        const unsigned int nMinMultiplier = nL1CacheElements * j;
        const unsigned int nMaxMultiplier = std::min(nL1CacheElements * (j + 1), nSieveSize);
		//if (tempwork.time != current_work.time)
		//	break;

        for (unsigned int nPrimeSeq = 1; nPrimeSeq < nPrimes; nPrimeSeq++)
        {
            unsigned int nPrime = vPrimes[nPrimeSeq];
            ProcessMultiplier(vfCompositeCunningham1A, nMinMultiplier, nMaxMultiplier, nPrime, vCunningham1AMultipliers[nPrimeSeq]);
        }

        for (unsigned int nPrimeSeq = 1; nPrimeSeq < nPrimes; nPrimeSeq++)
        {
            unsigned int nPrime = vPrimes[nPrimeSeq];
            ProcessMultiplier(vfCompositeCunningham1B, nMinMultiplier, nMaxMultiplier, nPrime, vCunningham1BMultipliers[nPrimeSeq]);
        }

        for (unsigned int nPrimeSeq = 1; nPrimeSeq < nPrimes; nPrimeSeq++)
        {
            unsigned int nPrime = vPrimes[nPrimeSeq];
            ProcessMultiplier(vfCompositeCunningham2A, nMinMultiplier, nMaxMultiplier, nPrime, vCunningham2AMultipliers[nPrimeSeq]);
        }

        for (unsigned int nPrimeSeq = 1; nPrimeSeq < nPrimes; nPrimeSeq++)
        {
            unsigned int nPrime = vPrimes[nPrimeSeq];
            ProcessMultiplier(vfCompositeCunningham2B, nMinMultiplier, nMaxMultiplier, nPrime, vCunningham2BMultipliers[nPrimeSeq]);
        }

        // Combine all the bitsets
        // vfCompositeCunningham1 = vfCompositeCunningham1A | vfCompositeCunningham1B
        // vfCompositeCunningham2 = vfCompositeCunningham2A | vfCompositeCunningham2B
        // vfCompositeBiTwin = vfCompositeCunningham1A | vfCompositeCunningham2A
        // vfCandidates = ~(vfCompositeCunningham1 & vfCompositeCunningham2 & vfCompositeBiTwin)
        {
            // Fast version
            const unsigned int nBytes = (nMaxMultiplier - nMinMultiplier + 7) / 8;
            unsigned long *lCandidates = (unsigned long *)vfCandidates + (nMinMultiplier / nWordBits);
            unsigned long *lCompositeCunningham1A = (unsigned long *)vfCompositeCunningham1A + (nMinMultiplier / nWordBits);
            unsigned long *lCompositeCunningham1B = (unsigned long *)vfCompositeCunningham1B + (nMinMultiplier / nWordBits);
            unsigned long *lCompositeCunningham2A = (unsigned long *)vfCompositeCunningham2A + (nMinMultiplier / nWordBits);
            unsigned long *lCompositeCunningham2B = (unsigned long *)vfCompositeCunningham2B + (nMinMultiplier / nWordBits);
            const unsigned int nLongs = (nBytes + sizeof(unsigned long) - 1) / sizeof(unsigned long);
            for (unsigned int i = 0; i < nLongs; i++)
            {
                lCandidates[i] = ~((lCompositeCunningham1A[i] | lCompositeCunningham1B[i]) &
                                (lCompositeCunningham2A[i] | lCompositeCunningham2B[i]) &
                                (lCompositeCunningham1A[i] | lCompositeCunningham2A[i]));
            }
        }
    }

    this->nPrimeSeq = nPrimes - 1;

    free(vfCompositeCunningham1A);
    free(vfCompositeCunningham1B);
    free(vfCompositeCunningham2A);
    free(vfCompositeCunningham2B);
    mpz_clear(mpzFixedFactor);

    return false;
}
