#ifndef CSIEVEOFERATOSTHENES_H
#define CSIEVEOFERATOSTHENES_H

#include "gmpxx.h"

// Sieve of Eratosthenes for proof-of-work mining
class CSieveOfEratosthenes
{
    unsigned int nSieveSize; // size of the sieve
    unsigned int nBits; // target of the prime chain to search for
    mpz_class mpzFixedFactor; // fixed factor to derive the chain

    // final set of candidates for probable primality checking
    unsigned long *vfCandidates;
    
    static const unsigned int nWordBits = 8 * sizeof(unsigned long);
    unsigned int nCandidatesWords;
    unsigned int nCandidatesBytes;

    unsigned int nPrimeSeq; // prime sequence number currently being processed
    unsigned int nCandidateCount; // cached total count of candidates
    unsigned int nCandidateMultiplier; // current candidate for power test
    
    unsigned int nChainLength;
    unsigned int nHalfChainLength;
    
    //CBlockIndex* pindexPrev;
    
    unsigned int GetWordNum(unsigned int nBitNum) {
        return nBitNum / nWordBits;
    }
    
    unsigned long GetBitMask(unsigned int nBitNum) {
        return 1UL << (nBitNum % nWordBits);
    }
    
    void AddMultiplier(unsigned int *vMultipliers, const unsigned int nSolvedMultiplier);

    void ProcessMultiplier(unsigned long *vfComposites, const unsigned int nMinMultiplier, const unsigned int nMaxMultiplier, const unsigned int nPrime, unsigned int *vMultipliers)
    {
#ifdef USE_ROTATE
        const unsigned int nRotateBits = nPrime % nWordBits;
        for (unsigned int i = 0; i < nHalfChainLength; i++)
        {
            unsigned int nVariableMultiplier = vMultipliers[i];
            if (nVariableMultiplier == 0xFFFFFFFF) break;
            unsigned long lBitMask = GetBitMask(nVariableMultiplier);
            for (; nVariableMultiplier < nMaxMultiplier; nVariableMultiplier += nPrime)
            {
                vfComposites[GetWordNum(nVariableMultiplier)] |= lBitMask;
                lBitMask = (lBitMask << nRotateBits) | (lBitMask >> (nWordBits - nRotateBits));
            }
            vMultipliers[i] = nVariableMultiplier;
        }
#else
        for (unsigned int i = 0; i < nHalfChainLength; i++)
        {
            unsigned int nVariableMultiplier = vMultipliers[i];
            if (nVariableMultiplier == 0xFFFFFFFF) break;
            for (; nVariableMultiplier < nMaxMultiplier; nVariableMultiplier += nPrime)
            {
                vfComposites[GetWordNum(nVariableMultiplier)] |= GetBitMask(nVariableMultiplier);
            }
            vMultipliers[i] = nVariableMultiplier;
        }
#endif
    }

public:
	bool inited;
	CSieveOfEratosthenes()
	{
		inited = false;
	}

    CSieveOfEratosthenes(unsigned int nSieveSize, unsigned int nBits, mpz_class& mpzHash, mpz_class& mpzFixedMultiplier)//, CBlockIndex* pindexPrev)
    {
		Init(nSieveSize,nBits,mpzHash,mpzFixedMultiplier);
    }
    
    ~CSieveOfEratosthenes()
    {
		Deinit();
    }
	
    unsigned long *vfCompositeCunningham1A;
    unsigned long *vfCompositeCunningham1B;
    unsigned long *vfCompositeCunningham2A;
    unsigned long *vfCompositeCunningham2B;

	void Init(unsigned int nSieveSize, unsigned int nBits, mpz_class& mpzHash, mpz_class& mpzFixedMultiplier)
	{
		if (inited)
			return;
        this->nSieveSize = nSieveSize;
        this->nBits = nBits;
        this->mpzFixedFactor = mpzFixedMultiplier * mpzHash;
        //this->pindexPrev = pindexPrev;
        nPrimeSeq = 0;
        nCandidateCount = 0;
        nCandidateMultiplier = 0;
        nCandidatesWords = (nSieveSize + nWordBits - 1) / nWordBits;
        nCandidatesBytes = nCandidatesWords * sizeof(unsigned long);
        vfCandidates = (unsigned long *)malloc(nCandidatesBytes);
        memset(vfCandidates, 0, nCandidatesBytes);
		
		vfCompositeCunningham1A = (unsigned long *)malloc(nCandidatesBytes);
		vfCompositeCunningham1B = (unsigned long *)malloc(nCandidatesBytes);
		vfCompositeCunningham2A = (unsigned long *)malloc(nCandidatesBytes);
		vfCompositeCunningham2B = (unsigned long *)malloc(nCandidatesBytes);
		
		inited = true;
	}
	void Deinit(bool whine = true)
	{
		if (!inited)
			return;
		free(vfCandidates);
		free(vfCompositeCunningham1A);
		free(vfCompositeCunningham1B);
		free(vfCompositeCunningham2A);
		free(vfCompositeCunningham2B);
		inited = false;
	}

    // Get total number of candidates for power test
    unsigned int GetCandidateCount()
    {
        if (nCandidateCount)
            return nCandidateCount;

        unsigned int nCandidates = 0;
#ifdef __GNUC__
        for (unsigned int i = 0; i < nCandidatesWords; i++)
        {
            nCandidates += __builtin_popcountl(vfCandidates[i]);
        }
#else
        for (unsigned int i = 0; i < nCandidatesWords; i++)
        {
            unsigned long lBits = vfCandidates[i];
            for (unsigned int j = 0; j < nWordBits; j++)
            {
                nCandidates += (lBits & 1UL);
                lBits >>= 1;
            }
        }
#endif
        nCandidateCount = nCandidates;
        return nCandidates;
    }

    // Scan for the next candidate multiplier (variable part)
    // Return values:
    //   True - found next candidate; nVariableMultiplier has the candidate
    //   False - scan complete, no more candidate and reset scan
    bool GetNextCandidateMultiplier(unsigned int& nVariableMultiplier)
    {
        unsigned long lBits = vfCandidates[GetWordNum(nCandidateMultiplier)];
        while(true)
        {
            nCandidateMultiplier++;
            if (nCandidateMultiplier >= nSieveSize)
            {
                nCandidateMultiplier = 0;
                return false;
            }
            if (nCandidateMultiplier % nWordBits == 0)
            {
                lBits = vfCandidates[GetWordNum(nCandidateMultiplier)];
                if (lBits == 0)
                {
                    // Skip an entire word
                    nCandidateMultiplier += nWordBits - 1;
                    continue;
                }
            }
            if (lBits & GetBitMask(nCandidateMultiplier))
            {
                nVariableMultiplier = nCandidateMultiplier;
                return true;
            }
        }
    }

    // Get progress percentage of the sieve
    unsigned int GetProgressPercentage();

    // Weave the sieve for the next prime in table
    // Return values:
    //   True  - weaved another prime; nComposite - number of composites removed
    //   False - sieve already completed
    bool Weave();
};



#endif
