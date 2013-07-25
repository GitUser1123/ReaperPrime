#include "Global.h"
#include "CPUAlgos.h"
#include "CPUAlgos_global.h"

vector<uchar> XPM_create_auxdata(mpz_t* bnChainOrigin)
{
	size_t exportsz, resultoff;
	uchar* ex_port = (uchar*)mpz_export(NULL, &exportsz, -1, 1, -1, 0, *bnChainOrigin);
	//assert(exportsz < 250);  // FIXME: bitcoin varint
	resultoff = 1;
	if (ex_port[0] & 0x80)
		++resultoff;
	uchar* result = new uchar[exportsz+resultoff];
	result[0] = exportsz + resultoff - 1;
	result[1] = '\0';
	memcpy(&result[resultoff], ex_port, exportsz);
	if (mpz_sgn(*bnChainOrigin) < 0)
		result[1] |= 0x80;
	free(ex_port);
	vector<uchar> vec(result,result+exportsz+resultoff);
	delete[]result;
	return vec;
}
