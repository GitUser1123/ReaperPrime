#include "Global.h"
#include "CPUMiner.h"
#include "CPUAlgos.h"
#include "Util.h"
#include "SHA256.h"
#include "CPUAlgos_global.h"

#include <iomanip>

typedef unsigned long long int uint64;
typedef long long int int64;

extern ullint chainspersec[20];
extern ullint totalpersec;

extern uint found0,foundtotal;

ullint fermats=0,gandalfs=0;


// Copyright (c) 2013 Primecoin developers
// Distributed under conditional MIT/X11 software license,
// see the accompanying file COPYING

// Copyright (c) 2013 Primecoin developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//START HEADER

#include <gmp.h>
#include <gmpxx.h>
#include <bitset>

static const unsigned int nMaxSievePercentage = 100;
static const unsigned int nDefaultSievePercentage = 10;
static const unsigned int nMinSievePercentage = 1;
extern unsigned int nSievePercentage;
static const unsigned int nMaxSieveSize = 10000000u;
static const unsigned int nDefaultSieveSize = 1000000u;
static const unsigned int nMinSieveSize = 100000u;
extern unsigned int nSieveSize;
//static const uint256 hashBlockHeaderLimit = (uint256(1) << 255);
static const mpz_class mpzOne = 1;
static const mpz_class mpzTwo = 2;
static const mpz_class mpzPrimeMax = (mpzOne << 2000) - 1;
static const mpz_class mpzPrimeMin = (mpzOne << 255);

// Estimate how many 5-chains are found per hour
static const unsigned int nStatsChainLength = 5;

extern unsigned int nTargetInitialLength;
extern unsigned int nTargetMinLength;

// Generate small prime table
void GeneratePrimeTable();
// Get next prime number of p
bool PrimeTableGetNextPrime(unsigned int& p);
// Get previous prime number of p
bool PrimeTableGetPreviousPrime(unsigned int& p);

// Compute primorial number p#
void Primorial(unsigned int p, mpz_class& mpzPrimorial);
// Compute Primorial number p#
// Fast 32-bit version assuming that p <= 23
unsigned int PrimorialFast(unsigned int p);
// Compute the first primorial number greater than or equal to bn
void PrimorialAt(mpz_class& bn, mpz_class& mpzPrimorial);

// Test probable prime chain for: bnPrimeChainOrigin
// fFermatTest
//   true - Use only Fermat tests
//   false - Use Fermat-Euler-Lagrange-Lifchitz tests
// Return value:
//   true - Probable prime chain found (one of nChainLength meeting target)
//   false - prime chain too short (none of nChainLength meeting target)
//bool ProbablePrimeChainTest(const CBigNum& bnPrimeChainOrigin, unsigned int nBits, bool fFermatTest, unsigned int& nChainLengthCunningham1, unsigned int& nChainLengthCunningham2, unsigned int& nChainLengthBiTwin);

static const unsigned int nFractionalBits = 24;
static const unsigned int TARGET_FRACTIONAL_MASK = (1u<<nFractionalBits) - 1;
static const unsigned int TARGET_LENGTH_MASK = ~TARGET_FRACTIONAL_MASK;
static const uint64 nFractionalDifficultyMax = (1llu << (nFractionalBits + 32));
static const uint64 nFractionalDifficultyMin = (1llu << 32);
static const uint64 nFractionalDifficultyThreshold = (1llu << (8 + 32));
static const unsigned int nWorkTransitionRatio = 32;
unsigned int TargetGetLimit();
unsigned int TargetGetInitial();
unsigned int TargetGetLength(unsigned int nBits);
bool TargetSetLength(unsigned int nLength, unsigned int& nBits);
unsigned int TargetGetFractional(unsigned int nBits);
uint64 TargetGetFractionalDifficulty(unsigned int nBits);
bool TargetSetFractionalDifficulty(uint64 nFractionalDifficulty, unsigned int& nBits);
std::string TargetToString(unsigned int nBits);
unsigned int TargetFromInt(unsigned int nLength);

// Mine probable prime chain of form: n = h * p# +/- 1
bool MineProbablePrimeChain(Reap_CPU_param* state, Work& tempwork, mpz_class& mpzFixedMultiplier, bool& fNewBlock, unsigned int& nTriedMultiplier, unsigned int& nProbableChainLength, unsigned int& nTests, unsigned int& nPrimesHit, unsigned int& nChainsHit, mpz_class& mpzHash, unsigned int nPrimorialMultiplier);

// Check prime proof-of-work
enum // prime chain type
{
    PRIME_CHAIN_CUNNINGHAM1 = 1u,
    PRIME_CHAIN_CUNNINGHAM2 = 2u,
    PRIME_CHAIN_BI_TWIN     = 3u,
};

// prime target difficulty value for visualization
double GetPrimeDifficulty(unsigned int nBits);
// Estimate work transition target to longer prime chain
unsigned int EstimateWorkTransition(unsigned int nPrevWorkTransition, unsigned int nBits, unsigned int nChainLength);
// prime chain type and length value
std::string GetPrimeChainName(unsigned int nChainType, unsigned int nChainLength);

#if defined(__i386__) || defined(_M_IX86) || defined(_X86_) || defined(__x86_64__) || defined(_M_X64)
#define USE_ROTATE
#endif

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
    CSieveOfEratosthenes(unsigned int nSieveSize, unsigned int nBits, mpz_class& mpzHash, mpz_class& mpzFixedMultiplier)//, CBlockIndex* pindexPrev)
    {
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
    }
    
    ~CSieveOfEratosthenes()
    {
        free(vfCandidates);
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

//START COPYPASTE FROM OTHER HEADERS
//util.h
static const int64 COIN = 100000000;
static const int64 CENT = 1000000;
//END COPYPASTE FROM OTHER HEADERS

// Prime Table
std::vector<unsigned int> vPrimes;
std::vector<unsigned int> vTwoInverses;
unsigned int nSieveSize = nDefaultSieveSize;
unsigned int nSievePercentage = nDefaultSievePercentage;

static unsigned int int_invert(unsigned int a, unsigned int nPrime);

void GeneratePrimeTable()
{
    //nSievePercentage = (unsigned int)GetArg("-sievepercentage", nDefaultSievePercentage);
	nSievePercentage = globalconfs.coin.config.GetValue<uint>("sievepercentage");
    nSievePercentage = std::max(std::min(nSievePercentage, nMaxSievePercentage), nMinSievePercentage);

    //nSieveSize = (unsigned int)GetArg("-sievesize", nDefaultSieveSize);
	nSieveSize = globalconfs.coin.config.GetValue<uint>("sievesize");
    nSieveSize = std::max(std::min(nSieveSize, nMaxSieveSize), nMinSieveSize);

    printf("GeneratePrimeTable() : setting nSievePercentage = %u, nSieveSize = %u\n", nSievePercentage, nSieveSize);
    const unsigned nPrimeTableLimit = nSieveSize;
    vPrimes.clear();
    // Generate prime table using sieve of Eratosthenes
    std::vector<bool> vfComposite (nPrimeTableLimit, false);
    for (unsigned int nFactor = 2; nFactor * nFactor < nPrimeTableLimit; nFactor++)
    {
        if (vfComposite[nFactor])
            continue;
        for (unsigned int nComposite = nFactor * nFactor; nComposite < nPrimeTableLimit; nComposite += nFactor)
            vfComposite[nComposite] = true;
    }
    for (unsigned int n = 2; n < nPrimeTableLimit; n++)
        if (!vfComposite[n])
            vPrimes.push_back(n);
    printf("GeneratePrimeTable() : prime table [1, %d] generated with %lu primes", nPrimeTableLimit, vPrimes.size());
    //BOOST_FOREACH(unsigned int nPrime, vPrimes)
    //    printf(" %u", nPrime);
    printf("\n");
    
    const unsigned int nPrimes = vPrimes.size();
    vTwoInverses = std::vector<unsigned int> (nPrimes, 0);
    for (unsigned int nPrimeSeq = 1; nPrimeSeq < nPrimes; nPrimeSeq++)
    {
        vTwoInverses[nPrimeSeq] = int_invert(2, vPrimes[nPrimeSeq]);
    }
}

// Get next prime number of p
bool PrimeTableGetNextPrime(unsigned int& p)
{
    //BOOST_FOREACH(unsigned int nPrime, vPrimes)
	for(uint i=0; i<vPrimes.size(); ++i)
    {
		unsigned int nPrime = vPrimes[i];
        if (nPrime > p)
        {
            p = nPrime;
            return true;
        }
    }
    return false;
}

// Get previous prime number of p
bool PrimeTableGetPreviousPrime(unsigned int& p)
{
    unsigned int nPrevPrime = 0;
	//BOOST_FOREACH(unsigned int nPrime, vPrimes)
	for(uint i=0; i<vPrimes.size(); ++i)
    {
		unsigned int nPrime = vPrimes[i];
        if (nPrime >= p)
            break;
        nPrevPrime = nPrime;
    }
    if (nPrevPrime)
    {
        p = nPrevPrime;
        return true;
    }
    return false;
}

// Compute Primorial number p#
void Primorial(unsigned int p, mpz_class& mpzPrimorial)
{
    unsigned long nPrimorial = 1;
    unsigned int i;
    if (sizeof(unsigned long) >= 8)
    {
        // Fast 64-bit loop if possible
        for (i = 0; i < 15; i++)
        {
            unsigned int nPrime = vPrimes[i];
            if (nPrime > p) break;
            nPrimorial *= nPrime;
        }
    }
    else
    {
        // Fast 32-bit loop first
        for (i = 0; i < 9; i++)
        {
            unsigned int nPrime = vPrimes[i];
            if (nPrime > p) break;
            nPrimorial *= nPrime;
        }
    }

    mpzPrimorial = nPrimorial;
    for (; i < vPrimes.size(); i++)
    {
        unsigned int nPrime = vPrimes[i];
        if (nPrime > p) break;
        mpzPrimorial *= nPrime;
    }
}

// Compute Primorial number p#
// Fast 32-bit version assuming that p <= 23
unsigned int PrimorialFast(unsigned int p)
{
    unsigned int nPrimorial = 1;
	//BOOST_FOREACH(unsigned int nPrime, vPrimes)
	for(uint i=0; i<vPrimes.size(); ++i)
    {
		unsigned int nPrime = vPrimes[i];
        if (nPrime > p) break;
        nPrimorial *= nPrime;
    }
    return nPrimorial;
}

// Compute first primorial number greater than or equal to pn
void PrimorialAt(mpz_class& bn, mpz_class& mpzPrimorial)
{
	//BOOST_FOREACH(unsigned int nPrime, vPrimes)
	for(uint i=0; i<vPrimes.size(); ++i)
    {
		unsigned int nPrime = vPrimes[i];
        mpzPrimorial *= nPrime;
        if (mpzPrimorial >= bn)
            return;
    }
}

// Proof-of-work Target (prime chain target):
//   format - 32 bit, 8 length bits, 24 fractional length bits

unsigned int nTargetInitialLength = 7; // initial chain length target
unsigned int nTargetMinLength = 6;     // minimum chain length target

unsigned int TargetGetLimit()
{
    return (nTargetMinLength << nFractionalBits);
}

unsigned int TargetGetInitial()
{
    return (nTargetInitialLength << nFractionalBits);
}

unsigned int TargetGetLength(unsigned int nBits)
{
    return ((nBits & TARGET_LENGTH_MASK) >> nFractionalBits);
}

bool TargetSetLength(unsigned int nLength, unsigned int& nBits)
{
    if (nLength >= 0xff)
	{
		throw string("TargetSetLength() : invalid length=")+ToString(nLength);
        //return error("TargetSetLength() : invalid length=%u", nLength);
	}
    nBits &= TARGET_FRACTIONAL_MASK;
    nBits |= (nLength << nFractionalBits);
    return true;
}

static void TargetIncrementLength(unsigned int& nBits)
{
    nBits += (1 << nFractionalBits);
}

static void TargetDecrementLength(unsigned int& nBits)
{
    if (TargetGetLength(nBits) > nTargetMinLength)
        nBits -= (1 << nFractionalBits);
}

unsigned int TargetGetFractional(unsigned int nBits)
{
    return (nBits & TARGET_FRACTIONAL_MASK);
}

uint64 TargetGetFractionalDifficulty(unsigned int nBits)
{
    return (nFractionalDifficultyMax / (uint64) ((1llu<<nFractionalBits) - TargetGetFractional(nBits)));
}

bool TargetSetFractionalDifficulty(uint64 nFractionalDifficulty, unsigned int& nBits)
{
    if (nFractionalDifficulty < nFractionalDifficultyMin)
	{
		cout << "TargetSetFractionalDifficulty() : difficulty below min" << endl;
	}
    uint64 nFractional = nFractionalDifficultyMax / nFractionalDifficulty;
    if (nFractional > (1u<<nFractionalBits))
	{
		cout << "TargetSetFractionalDifficulty() : fractional overflow: nFractionalDifficulty=" << nFractionalDifficulty << endl;
	}
    nFractional = (1u<<nFractionalBits) - nFractional;
    nBits &= TARGET_LENGTH_MASK;
    nBits |= (unsigned int)nFractional;
    return true;
}

std::string TargetToString(unsigned int nBits)
{
    //return strprintf("%02x.%06x", TargetGetLength(nBits), TargetGetFractional(nBits));
	stringstream ss;
	ss << std::hex << std::setw(2) << std::setfill('0') << TargetGetLength(nBits) << "." << std::setw(6) << std::setfill('0') << TargetGetFractional(nBits);
	return ss.str();
}

unsigned int TargetFromInt(unsigned int nLength)
{
    return (nLength << nFractionalBits);
}

// Number of primes to test with fast divisibility testing
static const unsigned int nFastDivPrimes = 30;

class CPrimalityTestParams
{
public:
    // GMP variables
    mpz_t mpzN;
    mpz_t mpzE;
    mpz_t mpzR;
    mpz_t mpzRplusOne;
    
    // GMP C++ variables
    mpz_class mpzOriginMinusOne;
    mpz_class mpzOriginPlusOne;
    mpz_class N;

    // Values specific to a round
    unsigned int nBits;
    unsigned int nPrimorialSeq;

    // This is currently always false when mining
    static const bool fFermatTest = false;

    // Results
    unsigned int nChainLengthCunningham1;
    unsigned int nChainLengthCunningham2;
    unsigned int nChainLengthBiTwin;

    CPrimalityTestParams(unsigned int nBits, unsigned int nPrimorialSeq)
    {
        this->nBits = nBits;
        this->nPrimorialSeq = nPrimorialSeq;
        nChainLengthCunningham1 = 0;
        nChainLengthCunningham2 = 0;
        nChainLengthBiTwin = 0;
        mpz_init(mpzN);
        mpz_init(mpzE);
        mpz_init(mpzR);
        mpz_init(mpzRplusOne);
    }

    ~CPrimalityTestParams()
    {
        mpz_clear(mpzN);
        mpz_clear(mpzE);
        mpz_clear(mpzR);
        mpz_clear(mpzRplusOne);
    }
};

// Check Fermat probable primality test (2-PRP): 2 ** (n-1) = 1 (mod n)
// true: n is probable prime
// false: n is composite; set fractional length in the nLength output
static bool FermatProbablePrimalityTestFast(const mpz_class& n, unsigned int& nLength, CPrimalityTestParams& testParams, bool fFastDiv = false)
{
    // Faster GMP version
    mpz_t& mpzN = testParams.mpzN;
    mpz_t& mpzE = testParams.mpzE;
    mpz_t& mpzR = testParams.mpzR;
    const unsigned int nPrimorialSeq = testParams.nPrimorialSeq;

    mpz_set(mpzN, n.get_mpz_t());
    if (fFastDiv)
    {
        // Fast divisibility tests
        // Starting from the first prime not included in the round primorial
        const unsigned int nBeginSeq = nPrimorialSeq + 1;
        const unsigned int nEndSeq = nBeginSeq + nFastDivPrimes;
        for (unsigned int nPrimeSeq = nBeginSeq; nPrimeSeq < nEndSeq; nPrimeSeq++) {
            if (mpz_divisible_ui_p(mpzN, vPrimes[nPrimeSeq])) {
                return false;
            }
        }
    }

	++fermats;
    mpz_sub_ui(mpzE, mpzN, 1);
    mpz_powm(mpzR, mpzTwo.get_mpz_t(), mpzE, mpzN);
    if (mpz_cmp_ui(mpzR, 1) == 0)
    {
        return true;
    }
    // Failed Fermat test, calculate fractional length
    mpz_sub(mpzE, mpzN, mpzR);
    mpz_mul_2exp(mpzR, mpzE, nFractionalBits);
    mpz_tdiv_q(mpzE, mpzR, mpzN);
    unsigned int nFractionalLength = mpz_get_ui(mpzE);

    if (nFractionalLength >= (1 << nFractionalBits))
	{
		cout << "FermatProbablePrimalityTest() : fractional assert" << endl;
        return false;
	}
    nLength = (nLength & TARGET_LENGTH_MASK) | nFractionalLength;
    return false;
}

// Test probable primality of n = 2p +/- 1 based on Euler, Lagrange and Lifchitz
// fSophieGermain:
//   true:  n = 2p+1, p prime, aka Cunningham Chain of first kind
//   false: n = 2p-1, p prime, aka Cunningham Chain of second kind
// Return values
//   true: n is probable prime
//   false: n is composite; set fractional length in the nLength output
static bool EulerLagrangeLifchitzPrimalityTestFast(const mpz_class& n, bool fSophieGermain, unsigned int& nLength, CPrimalityTestParams& testParams, bool fFastDiv = false)
{
    // Faster GMP version
    mpz_t& mpzN = testParams.mpzN;
    mpz_t& mpzE = testParams.mpzE;
    mpz_t& mpzR = testParams.mpzR;
    mpz_t& mpzRplusOne = testParams.mpzRplusOne;
    const unsigned int nPrimorialSeq = testParams.nPrimorialSeq;

    mpz_set(mpzN, n.get_mpz_t());
    if (fFastDiv)
    {
        // Fast divisibility tests
        // Starting from the first prime not included in the round primorial
        const unsigned int nBeginSeq = nPrimorialSeq + 1;
        const unsigned int nEndSeq = nBeginSeq + nFastDivPrimes;
        for (unsigned int nPrimeSeq = nBeginSeq; nPrimeSeq < nEndSeq; nPrimeSeq++) {
            if (mpz_divisible_ui_p(mpzN, vPrimes[nPrimeSeq])) {
                return false;
            }
        }
    }
	++gandalfs;
    mpz_sub_ui(mpzE, mpzN, 1);
    mpz_tdiv_q_2exp(mpzE, mpzE, 1);
    mpz_powm(mpzR, mpzTwo.get_mpz_t(), mpzE, mpzN);
    unsigned int nMod8 = mpz_tdiv_ui(mpzN, 8);
    bool fPassedTest = false;
    if (fSophieGermain && (nMod8 == 7)) // Euler & Lagrange
        fPassedTest = !mpz_cmp_ui(mpzR, 1);
    else if (fSophieGermain && (nMod8 == 3)) // Lifchitz
    {
        mpz_add_ui(mpzRplusOne, mpzR, 1);
        fPassedTest = !mpz_cmp(mpzRplusOne, mpzN);
    }
    else if ((!fSophieGermain) && (nMod8 == 5)) // Lifchitz
    {
        mpz_add_ui(mpzRplusOne, mpzR, 1);
        fPassedTest = !mpz_cmp(mpzRplusOne, mpzN);
    }
    else if ((!fSophieGermain) && (nMod8 == 1)) // LifChitz
        fPassedTest = !mpz_cmp_ui(mpzR, 1);
    else
	{
		cout << "EulerLagrangeLifchitzPrimalityTest() : invalid n %% 8 = " << nMod8 << ", " << (fSophieGermain? "first kind" : "second kind") << endl;
		return false;
        //return error("EulerLagrangeLifchitzPrimalityTest() : invalid n %% 8 = %d, %s", nMod8, (fSophieGermain? "first kind" : "second kind"));
	}
    
    if (fPassedTest)
    {
        return true;
    }
    
    // Failed test, calculate fractional length
    mpz_mul(mpzE, mpzR, mpzR);
    mpz_tdiv_r(mpzR, mpzE, mpzN); // derive Fermat test remainder

    mpz_sub(mpzE, mpzN, mpzR);
    mpz_mul_2exp(mpzR, mpzE, nFractionalBits);
    mpz_tdiv_q(mpzE, mpzR, mpzN);
    unsigned int nFractionalLength = mpz_get_ui(mpzE);
    
    if (nFractionalLength >= (1 << nFractionalBits))
	{
		cout << "EulerLagrangeLifchitzPrimalityTest() : fractional assert" << endl;
        return false;
	}
    nLength = (nLength & TARGET_LENGTH_MASK) | nFractionalLength;
    return false;
}

// Test Probable Cunningham Chain for: n
// fSophieGermain:
//   true - Test for Cunningham Chain of first kind (n, 2n+1, 4n+3, ...)
//   false - Test for Cunningham Chain of second kind (n, 2n-1, 4n-3, ...)
// Return value:
//   true - Probable Cunningham Chain found (length at least 2)
//   false - Not Cunningham Chain
static bool ProbableCunninghamChainTestFast(const mpz_class& n, bool fSophieGermain, bool fFermatTest, unsigned int& nProbableChainLength, CPrimalityTestParams& testParams)
{
    nProbableChainLength = 0;
    mpz_class &N = testParams.N;
    N = n;

    // Fermat test for n first
    if (!FermatProbablePrimalityTestFast(N, nProbableChainLength, testParams, true))
        return false;

    // Euler-Lagrange-Lifchitz test for the following numbers in chain
    while (true)
    {
        TargetIncrementLength(nProbableChainLength);
        N = N + N + (fSophieGermain? 1 : (-1));
        if (fFermatTest)
        {
            if (!FermatProbablePrimalityTestFast(N, nProbableChainLength, testParams, true))
                break;
        }
        else
        {
            if (!EulerLagrangeLifchitzPrimalityTestFast(N, fSophieGermain, nProbableChainLength, testParams, true))
                break;
        }
    }
    return (TargetGetLength(nProbableChainLength) >= 2);
}

// Test probable prime chain for: nOrigin
// Return value:
//   true - Probable prime chain found (one of nChainLength meeting target)
//   false - prime chain too short (none of nChainLength meeting target)
static bool ProbablePrimeChainTestFast(const mpz_class& mpzPrimeChainOrigin, CPrimalityTestParams& testParams)
{
    const unsigned int nBits = testParams.nBits;
	const unsigned int nBits_masked = nBits&TARGET_LENGTH_MASK;
    unsigned int& nChainLengthCunningham1 = testParams.nChainLengthCunningham1;
    unsigned int& nChainLengthCunningham2 = testParams.nChainLengthCunningham2;
    unsigned int& nChainLengthBiTwin = testParams.nChainLengthBiTwin;
    const bool fFermatTest = testParams.fFermatTest;
    mpz_class& mpzOriginMinusOne = testParams.mpzOriginMinusOne;
    mpz_class& mpzOriginPlusOne = testParams.mpzOriginPlusOne;
    nChainLengthCunningham1 = 0;
    nChainLengthCunningham2 = 0;
    nChainLengthBiTwin = 0;

    // Test for Cunningham Chain of first kind
    mpzOriginMinusOne = mpzPrimeChainOrigin - 1;
    ProbableCunninghamChainTestFast(mpzOriginMinusOne, true, fFermatTest, nChainLengthCunningham1, testParams);
	if ((nChainLengthCunningham1&TARGET_FRACTIONAL_MASK) == 0)
		nChainLengthCunningham1 |= TARGET_FRACTIONAL_MASK;
    // Test for Cunningham Chain of second kind
    mpzOriginPlusOne = mpzPrimeChainOrigin + 1;
    ProbableCunninghamChainTestFast(mpzOriginPlusOne, false, fFermatTest, nChainLengthCunningham2, testParams);
	if ((nChainLengthCunningham2&TARGET_FRACTIONAL_MASK) == 0)
		nChainLengthCunningham2 |= TARGET_FRACTIONAL_MASK;
	// Figure out BiTwin Chain length
    // BiTwin Chain allows a single prime at the end for odd length chain
    nChainLengthBiTwin =
        (TargetGetLength(nChainLengthCunningham1) > TargetGetLength(nChainLengthCunningham2))?
            (nChainLengthCunningham2 + TargetFromInt(TargetGetLength(nChainLengthCunningham2)+1)) :
            (nChainLengthCunningham1 + TargetFromInt(TargetGetLength(nChainLengthCunningham1)));
			
	uint c1 = TargetGetLength(nChainLengthCunningham1);
	uint c2 = TargetGetLength(nChainLengthCunningham2);
	uint tw = TargetGetLength(nChainLengthBiTwin);
	
	if (c1 >= 6)
	{
		cout << "C1 " << nChainLengthCunningham1 << " --> " << TargetToString(nChainLengthCunningham1) << " found!" << endl;
	}
	if (c2 >= 6)
	{
		cout << "C2 " << nChainLengthCunningham2 << " --> " << TargetToString(nChainLengthCunningham2) << " found!" << endl;
	}
	if (tw >= 6)
	{
		cout << "TW " << nChainLengthBiTwin << " --> " << TargetToString(nChainLengthBiTwin) << " found!" << endl;
	}
	
	++chainspersec[c1];
	++chainspersec[c2];
	++chainspersec[tw];
	++totalpersec;

    return (nChainLengthCunningham1 >= nBits || nChainLengthCunningham2 >= nBits || nChainLengthBiTwin >= nBits);
}

// Mine probable prime chain of form: n = h * p# +/- 1
bool MineProbablePrimeChain(Reap_CPU_param* state, Work& tempwork, CSieveOfEratosthenes** psieve, mpz_class& mpzFixedMultiplier, bool& fNewBlock, unsigned int& nTriedMultiplier, unsigned int& nProbableChainLength, unsigned int& nTests, unsigned int& nPrimesHit, unsigned int& nChainsHit, mpz_class& mpzHash, unsigned int nPrimorialMultiplier)
{
    CSieveOfEratosthenes *lpsieve;
    nProbableChainLength = 0;
    nTests = 0;
    nPrimesHit = 0;
    nChainsHit = 0;
    //const unsigned int nBits = block.nBits;
	const unsigned int nBits = *(uint*)&tempwork.data[72];

    if (fNewBlock && *psieve != NULL)
    {
        // Must rebuild the sieve
		delete *psieve;
		*psieve = NULL;
        //psieve.reset();
    }
    fNewBlock = false;

    int64 nStart; // microsecond timer
    //CBlockIndex* pindexPrev = pindexBest;
    if ((lpsieve = *psieve) == NULL)
    {
        // Build sieve
        nStart = ticker()*1000;
        lpsieve = new CSieveOfEratosthenes(nSieveSize, nBits, mpzHash, mpzFixedMultiplier);
        while (lpsieve->Weave())
		{
			if (tempwork.time != current_work.time)
				break;
		}
        if (globalconfs.coin.config.GetValue<bool>("printmining"))
            printf("MineProbablePrimeChain() : new sieve (%u/%u@%u%%) ready in %uus\n", lpsieve->GetCandidateCount(), nSieveSize, lpsieve->GetProgressPercentage(), (unsigned int) (ticker()*1000 - nStart));
        *psieve = lpsieve;
    }

    mpz_class mpzHashMultiplier = mpzHash * mpzFixedMultiplier;
    mpz_class mpzChainOrigin;
    
    // Count the number of candidates produced by the sieve
    unsigned int nCandidates = lpsieve->GetCandidateCount();
    
    // Determine the sequence number of the round primorial
    unsigned int nPrimorialSeq = 0;
    while (vPrimes[nPrimorialSeq + 1] <= nPrimorialMultiplier)
        nPrimorialSeq++;

    // Allocate GMP variables for primality tests
    CPrimalityTestParams testParams(nBits, nPrimorialSeq);

    nStart = ticker()*1000;
    
    // References to counters;
    unsigned int& nChainLengthCunningham1 = testParams.nChainLengthCunningham1;
    unsigned int& nChainLengthCunningham2 = testParams.nChainLengthCunningham2;
    unsigned int& nChainLengthBiTwin = testParams.nChainLengthBiTwin;

    // Process the sieve in 10 parts
    while (nTests < (nCandidates + 9) / 10)
    {
		if (tempwork.time != current_work.time)
			break;
        nTests++;
        if (!lpsieve->GetNextCandidateMultiplier(nTriedMultiplier))
        {
            // power tests completed for the sieve
            //if (fDebug && GetBoolArg("-printmining"))
                //printf("MineProbablePrimeChain() : %u tests (%u primes and %u %d-chains) in %uus\n", nTests, nPrimesHit, nChainsHit, nStatsChainLength, (unsigned int) (GetTimeMicros() - nStart));
            //psieve.reset();
			delete *psieve;
			*psieve = NULL;
            fNewBlock = true; // notify caller to change nonce
            return false;
        }
        mpzChainOrigin = mpzHashMultiplier * nTriedMultiplier;
        nChainLengthCunningham1 = 0;
        nChainLengthCunningham2 = 0;
        nChainLengthBiTwin = 0;
        if (ProbablePrimeChainTestFast(mpzChainOrigin, testParams))
        {
			mpz_t mpzPrimeChainMultiplier; mpz_init(mpzPrimeChainMultiplier);
			mpz_mul_ui(mpzPrimeChainMultiplier,mpzFixedMultiplier.get_mpz_t(),nTriedMultiplier);
			{
				vector<uchar> auxdata = XPM_create_auxdata(&mpzPrimeChainMultiplier);
				CPU_Got_share(state,tempwork,auxdata);
			}
			mpz_clear(mpzPrimeChainMultiplier);
			
            nProbableChainLength = std::max(std::max(nChainLengthCunningham1, nChainLengthCunningham2), nChainLengthBiTwin);
            return true;
        }
        nProbableChainLength = std::max(std::max(nChainLengthCunningham1, nChainLengthCunningham2), nChainLengthBiTwin);
        if(TargetGetLength(nProbableChainLength) >= 1)
            nPrimesHit++;
        if(TargetGetLength(nProbableChainLength) >= nStatsChainLength)
            nChainsHit++;
    }
    
    //if (fDebug && GetBoolArg("-printmining"))
        //printf("MineProbablePrimeChain() : %u tests (%u primes and %u %d-chains) in %uus\n", nTests, nPrimesHit, nChainsHit, nStatsChainLength, (unsigned int) (GetTimeMicros() - nStart));
    
    return false; // stop as new block arrived
}

// prime target difficulty value for visualization
double GetPrimeDifficulty(unsigned int nBits)
{
    return ((double) nBits / (double) (1 << nFractionalBits));
}

// Estimate work transition target to longer prime chain
unsigned int EstimateWorkTransition(unsigned int nPrevWorkTransition, unsigned int nBits, unsigned int nChainLength)
{
    int64 nInterval = 500;
    int64 nWorkTransition = nPrevWorkTransition;
    unsigned int nBitsCeiling = 0;
    TargetSetLength(TargetGetLength(nBits)+1, nBitsCeiling);
    unsigned int nBitsFloor = 0;
    TargetSetLength(TargetGetLength(nBits), nBitsFloor);
    uint64 nFractionalDifficulty = TargetGetFractionalDifficulty(nBits);
    bool fLonger = (TargetGetLength(nChainLength) > TargetGetLength(nBits));
    if (fLonger)
        nWorkTransition = (nWorkTransition * (((nInterval - 1) * nFractionalDifficulty) >> 32) + 2 * ((uint64) nBitsFloor)) / ((((nInterval - 1) * nFractionalDifficulty) >> 32) + 2);
    else
        nWorkTransition = ((nInterval - 1) * nWorkTransition + 2 * ((uint64) nBitsCeiling)) / (nInterval + 1);
    return nWorkTransition;
}

// prime chain type and length value
std::string GetPrimeChainName(unsigned int nChainType, unsigned int nChainLength)
{
	return (nChainType==PRIME_CHAIN_CUNNINGHAM1)? "1CC" : ((nChainType==PRIME_CHAIN_CUNNINGHAM2)? "2CC" : "TWN") + TargetToString(nChainLength);

    //return strprintf("%s%s", (nChainType==PRIME_CHAIN_CUNNINGHAM1)? "1CC" : ((nChainType==PRIME_CHAIN_CUNNINGHAM2)? "2CC" : "TWN"), TargetToString(nChainLength).c_str());
}


// Get progress percentage of the sieve
unsigned int CSieveOfEratosthenes::GetProgressPercentage()
{
    return std::min(100u, (((nPrimeSeq >= vPrimes.size())? nSieveSize : vPrimes[nPrimeSeq]) * 100 / nSieveSize));
}

static unsigned int int_invert(unsigned int a, unsigned int nPrime)
{
    // Extended Euclidean algorithm to calculate the inverse of a in finite field defined by nPrime
    int rem0 = nPrime, rem1 = a % nPrime, rem2;
    int aux0 = 0, aux1 = 1, aux2;
    int quotient, inverse;

    while (1)
    {
        if (rem1 <= 1)
        {
            inverse = aux1;
            break;
        }

        rem2 = rem0 % rem1;
        quotient = rem0 / rem1;
        aux2 = -quotient * aux1 + aux0;

        if (rem2 <= 1)
        {
            inverse = aux2;
            break;
        }

        rem0 = rem1 % rem2;
        quotient = rem1 / rem2;
        aux0 = -quotient * aux2 + aux1;

        if (rem0 <= 1)
        {
            inverse = aux0;
            break;
        }

        rem1 = rem2 % rem0;
        quotient = rem2 / rem0;
        aux1 = -quotient * aux0 + aux2;
    }

    return (inverse + nPrime) % nPrime;
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

bool MinePrime_hp(Reap_CPU_param* state, Work& tempwork)
{
	uchar* tempdata = &tempwork.data[0];
	uchar hash[32];
	mysha256(hash,tempdata,80);
	mysha256(hash,hash,32);
	
	uint nBits = *(uint*)&tempdata[72];
	
	if (!(hash[31] & 0x80))
		return false; //hash is too small, abort

	Mpz_w hashnum;
	
	set_mpz_to_hash(&hashnum.n, hash);
	
	bool found = false;
	
	//START HP7 CODE
	CSieveOfEratosthenes* psieve = NULL;
	static const unsigned int nPrimorialHashFactor = 7;
    unsigned int nPrimorialMultiplier = nPrimorialHashFactor;	
	unsigned int nHashFactor = PrimorialFast(nPrimorialHashFactor);
    int64 nTimeExpected = 0;   // time expected to prime chain (micro-second)
    int64 nTimeExpectedPrev = 0; // time expected to prime chain last time
    bool fIncrementPrimorial = true; // increase or decrease primorial factor

	while(true)
	{
		if (tempwork.time != current_work.time)
			break;
        int64 nStart = ticker()/1000;
        bool fNewBlock = true;
        unsigned int nTriedMultiplier = 0;

        // Primecoin: try to find hash divisible by primorial
        unsigned int nHashFactor = PrimorialFast(nPrimorialHashFactor);

        // Based on mustyoshi's patch from https://bitcointalk.org/index.php?topic=251850.msg2689981#msg2689981
        mpz_class mpzHash;
        while(true) {

            // Check that the hash meets the minimum

            // Check that the hash is divisible by the fixed primorial
			mpzHash = mpz_class(hashnum.n);
            //mpz_set_uint256(mpzHash.get_mpz_t(), phash);
            if (!mpz_divisible_ui_p(mpzHash.get_mpz_t(), nHashFactor)) {
				return false;
            }

            // Use the hash that passed the tests
            break;
        }
        // Primecoin: primorial fixed multiplier
        mpz_class mpzPrimorial;
        unsigned int nRoundTests = 0;
        unsigned int nRoundPrimesHit = 0;
        int64 nPrimeTimerStart = ticker()*1000;
        Primorial(nPrimorialMultiplier, mpzPrimorial);

		gmp_printf("mpzPrimorial %Zd\n", mpzPrimorial.get_mpz_t());
		
        while(true)
        {
			if (tempwork.time != current_work.time)
				break;

            unsigned int nTests = 0;
            unsigned int nPrimesHit = 0;
            unsigned int nChainsHit = 0;

            // Primecoin: adjust round primorial so that the generated prime candidates meet the minimum
            mpz_class mpzMultiplierMin = mpzPrimeMin * nHashFactor / mpzHash + 1;
            while (mpzPrimorial < mpzMultiplierMin)
            {
                if (!PrimeTableGetNextPrime(nPrimorialMultiplier))
                    printf("PrimecoinMiner() : primorial minimum overflow");
                Primorial(nPrimorialMultiplier, mpzPrimorial);
            }
            mpz_class mpzFixedMultiplier;
            if (mpzPrimorial > nHashFactor) {
                mpzFixedMultiplier = mpzPrimorial / nHashFactor;
            } else {
                mpzFixedMultiplier = 1;
            }

            // Primecoin: mine for prime chain
            unsigned int nProbableChainLength;
            if (MineProbablePrimeChain(state, tempwork, &psieve, mpzFixedMultiplier, fNewBlock, nTriedMultiplier, nProbableChainLength, nTests, nPrimesHit, nChainsHit, mpzHash, nPrimorialMultiplier))
            {
				return true;
                /*SetThreadPriority(THREAD_PRIORITY_NORMAL);
                CheckWork(pblock, *pwalletMain, reservekey);
                SetThreadPriority(THREAD_PRIORITY_LOWEST);*/
                break;
            }
            nRoundTests += nTests;
            nRoundPrimesHit += nPrimesHit;

            if (fNewBlock)
            {
                // Primecoin: a sieve+primality round completes
                // Primecoin: estimate time to block
                int64 nRoundTime = (ticker()*1000 - nPrimeTimerStart); 
                nTimeExpected = nRoundTime / max(1u, nRoundTests);
                nTimeExpected = nTimeExpected * max(1u, nRoundTests) / max(1u, nRoundPrimesHit);
                for (unsigned int n = 1; n < TargetGetLength(nBits); n++)
                    nTimeExpected = nTimeExpected * max(1u, nRoundTests) * 3 / max(1u, nRoundPrimesHit);
                if (globalconfs.coin.config.GetValue<bool>("printmining"))
                    printf("PrimecoinMiner() : Round primorial=%u tests=%u primes=%u time=%uus expect=%us\n", nPrimorialMultiplier, nRoundTests, nRoundPrimesHit, (unsigned int) nRoundTime, (unsigned int)(nTimeExpected/1000000));

                /*

                // Primecoin: reset sieve+primality round timer
                nRoundTests = 0;
                nRoundPrimesHit = 0;
                nPrimeTimerStart = GetTimeMicros();
                if (nTimeExpected > nTimeExpectedPrev)
                    fIncrementPrimorial = !fIncrementPrimorial;
                nTimeExpectedPrev = nTimeExpected;
				*/
                // Primecoin: dynamic adjustment of primorial multiplier
                if (fIncrementPrimorial)
                {
                    if (!PrimeTableGetNextPrime(nPrimorialMultiplier))
                        printf("PrimecoinMiner() : primorial increment overflow");
                }
                else if (nPrimorialMultiplier > nPrimorialHashFactor)
                {
                    if (!PrimeTableGetPreviousPrime(nPrimorialMultiplier))
                        printf("PrimecoinMiner() : primorial decrement overflow");
                }
                Primorial(nPrimorialMultiplier, mpzPrimorial);
				
				return false;
            }
        }
	}
	
	//END HP7 CODE
	return found;
}

void* Reap_CPU_XPM_hp7(void* param)
{

	Reap_CPU_param* state = (Reap_CPU_param*)param;

	Work tempwork;
	tempwork.time = 13371337;

	//uchar tempdata[80];
	//memset(tempdata, 0, 80);

	uchar finalhash[32];
	uchar temphash[32];
	uchar hash_results[1] = {};

	uint current_server_id;
	
	uint starttime = ticker();
	uint currenttime = starttime;
	
	uint foundprimes=0;

	while(!shutdown_now)
	{
		if (current_work.old)
		{
			Wait_ms(20);
			continue;
		}
		if (tempwork.time != current_work.time)
		{
			pthread_mutex_lock(&current_work_mutex);
			tempwork = current_work;
			pthread_mutex_unlock(&current_work_mutex);
			//memcpy(tempdata, &tempwork.data[0], 80);

			*(uint*)&tempwork.data[76] = state->thread_id<<28;
			current_server_id = tempwork.server_id;

		}


		uint trues=0;
		
		for(uint h=0; h<CPU_BATCH_SIZE; ++h)
		{
		
			bool result = MinePrime_hp(state,tempwork);
			if (result) 
			{
				foundprimes++;
				pthread_mutex_lock(&current_work_mutex);
				current_work.old = true;
				pthread_mutex_unlock(&current_work_mutex);
				break;
			}
			
			++*(uint*)&tempwork.data[76];
		}
		//cout << "Every " << double(CPU_BATCH_SIZE)/double(trues) << "th num is true" << endl;

		state->hashes += CPU_BATCH_SIZE;
	}
	pthread_exit(NULL);
	return NULL;
}
