#include<stdint.h>
#include<stdlib.h>
#include<stdio.h>


/**		Coded multiplication of two 16-bit unsigned integers.
*		It is assumed that the result fits into a 16-bit integer too.
*
*		The input must be encoded as follows:
*		xc = A*x + Bx +D;
*		yc = A*y + By +D;
*
*		Prerequisites:
*		A == 31541 = 0x7b35
*		0 <= D   < 0x100000000			(arbitrary 32-bit value)
*		0 <= x, y, x*y   < 0x10000		(arbitrary 16-bit value)
*		0 < Bx, By, Bz < A
*
*		The expected result is:
*		zc = A*(x*y) + Bz + D;
*
*		Note: 0xEF203F1D*A = 1 when calculated with 32 bits.
*/
uint32_t codedMUL_uint16(uint32_t xc, uint32_t yc, uint32_t D,
						 uint32_t Bx, uint32_t By, uint32_t Bz){
	const uint32_t A = 0x7b35;
	uint32_t rc  = xc * yc;
	uint32_t t1  = (By+D)*xc + (Bx+D)*yc - Bx*By - Bz*A;
	uint32_t t2  = (Bx+By + A)*D + D*D;
	uint32_t Azc = rc - t1 + t2;
	uint32_t zc  = 0xEF203F1D*Azc;
	return zc;
}

uint32_t rand8(){ // random number in the range 0 ... 0xFF
	return (uint32_t) (rand() % 0x100);
}

uint32_t rand16(){ // random number in the range 0 ... 0xFFFF
	uint32_t low  = rand8();
	uint32_t high = rand8();	
	return (high << 8) + low;
}

uint32_t rand32(){ // random number in the range 0 ... 0xFFFFFFFF
	uint32_t low  = rand16();
	uint32_t high = rand16();	
	return (high << 16) + low;
}

uint32_t randB(){ // random number in the range 1 ... 0x7b34
	return (rand16() % 0x7b34) + 1;
}


/**		Simple test that runs the coded multiplcation 1000 times.
*
*		x,y are chosen randomly.
*		Bx,By,Bz are chosen randomly.
*		D is chosen randomly.
*
*		x,y are always less than 256, avoiding any overflows.
*
*		In practice, one would also test all edge cases, and 
*		choose the distribution of the random variables more carefully
*		(e.g. also allowing x, y to be greater than 256, as longs as x*y
*		 is still small enough)
*/
int main(){
	int failed = 0;
	int global_failed = 0;
	uint32_t D=0;
	uint32_t x=2,y=3,z;
	uint32_t xc, yc, zc;
	uint32_t Bx=0, By=0, Bz=0;
	const uint32_t A = 0x7b35;
	
	printf("run\t x\t y\t Bx\t By\t Bz\t D\t \tx*y\t z\tTest passed?\n");
	for(int i=0;i<1000;i++){
		failed = 0;
		D = rand32();
		x = rand8();
		y = rand8();
		Bx = randB(); By = randB(); Bz = randB();
		
		xc = A*x + Bx +D;
		yc = A*y + By +D;
		zc = codedMUL_uint16(xc,yc,D,Bx,By,Bz);
		z = zc-Bz-D; //decode zc (step 1)
		if(z%A!=0) 	  failed=1;	// zc was not a valid codeword
		z = z / A;	 //decode zc (step 2)
		if(z!=x*y)    failed=1; // z is not the product x*y
		
		if(failed){
			printf("%d\t %d\t %d\t %d\t %d\t %d\t %08x \t%d\t %u\t%s\n",
					i,   x,    y,   Bx, By,  Bz,  D,   x*y,   z, "failed");
		}else{
			printf("%d\t %d\t %d\t %d\t %d\t %d\t %08x \t%d\t %u\t%s\n",
					i,   x,    y,   Bx, By,  Bz,  D,   x*y,   z, "passed");
		}
		if(failed) global_failed=1;
	}	
	if(global_failed) 	printf("There were failed tests.\n");
	else				printf("All tests passed.\n");
}