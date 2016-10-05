#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <gmpxx.h>
#include <utility>
#include "ec_ops.h"
using namespace std;

Zp Zp::inverse() const{
	// Implement the Extended Euclidean Algorithm to return the inverse mod PRIME		
	mpz_class rnm1(value);
	mpz_class rn(PRIME);
	mpz_class xnm1(1);
	mpz_class xn(0);
	mpz_class qn;
	mpz_class xTemp;
	mpz_class theTemp=rnm1%rn;

	while(theTemp!=0)
	{
		qn=rnm1/rn;
		rnm1=rn;
		rn=theTemp;
		xTemp=xn;
		xn=xnm1-qn*xn;
		xnm1=xTemp;
		theTemp=rnm1%rn;
	}
	while(xn<0) {xn+=PRIME;}
	Zp result(xn);
	return result;
}


ECpoint ECpoint::operator + (const ECpoint &a) const {
	// Implement  elliptic curve addition 		
	if(this->infinityPoint||a.infinityPoint)
	{
		return *this;
	}
	if((this->x==a.x&&this->y==a.y)&&!(Zp(2)*(this->y)==0))
	{
		mpz_class x(this->x.getValue());
		mpz_class y(this->y.getValue());
		mpz_class lambda((3*x*x+A)*Zp(2*y).inverse().getValue());
		lambda%=PRIME;
		mpz_class xr(lambda*lambda-2*x+2*PRIME);
		xr%=PRIME;
		mpz_class yr(lambda*(x-xr+PRIME)-y+PRIME);
		yr%=PRIME;
		ECpoint result(xr,yr);
		return result;
	}
	if(!(this->x==a.x&&this->y==a.y)&&!(this->x==a.x))
	{
		mpz_class xp(this->x.getValue());
		mpz_class xq(a.x.getValue());
		mpz_class yp(this->y.getValue());
		mpz_class yq(a.y.getValue());
		mpz_class lambda((yq-yp+PRIME)*Zp(xq-xp+PRIME).inverse().getValue());
		lambda%=PRIME;
		mpz_class xr(lambda*lambda-xp-xq+2*PRIME);
		xr%=PRIME;		
		mpz_class yr(lambda*(xp-xr+PRIME)-yp+PRIME);
		yr%=PRIME;		
		ECpoint result(xr,yr);
		return result;
	}
	ECpoint result(true);
	return result;
}


ECpoint ECpoint::repeatSum(ECpoint p, mpz_class v) const {
	//Implement repeated squaring (with + rather than *) to find the sum of p+p+...+p (vtimes)
	//It is similar to the recursive exponential algorithm discussed for RSA		
	if(v==0)
	{
		ECpoint result(true);
		return result;
	}
	if(v==1)
	{
		return p;
	}
	ECpoint result=p;
	mpz_class temp=v;
	mpz_class times;
	mpz_class tempT=2;
	while(tempT<=temp)
	{
		result=result+result;
		times=tempT;
		tempT=times*2;
	}
	temp=temp-times;
	return result+repeatSum(p,temp);
}

Zp ECsystem::power(Zp val, mpz_class pow) {
	//Implement repeated squaring (*) to find the sum of val*val+...+val (pow times)
	//It is similar to the repeat sum above or recursive exponential algorithm discussed for RSA
	//It is the power function that is required to compute the square root in decryption algorithm
	if(pow==0)
	{
		return 1;
	}
	if(pow==1)
	{
		return val;
	}
	Zp result=val;
	mpz_class temp=pow;
	mpz_class times;
	mpz_class tempT=2;
	while(tempT<=temp)
	{
		result=result*result;
		times=tempT;
		tempT=times*2;
	}
	temp=temp-times;
	return result*power(val,temp);
}


mpz_class ECsystem::pointCompress(ECpoint e) {
	//It is the gamma function explained in the assignment.
	//Note: Here return type is mpz_class because the function may
	//map to a value greater than the defined PRIME number (i.e, range of Zp)
	//This function is fully defined.	
	mpz_class compressedPoint = e.x.getValue();
	compressedPoint = compressedPoint<<1;
	
	if(e.infinityPoint) {
		cout<<"Point cannot be compressed as its INF-POINT"<<flush;
		abort();
		}
	else {
		if (e.y.getValue()%2 == 1)
			compressedPoint = compressedPoint + 1;
		}
		//cout<<"For point  "<<e<<"  Compressed point is <<"<<compressedPoint<<"\n";
		return compressedPoint;

}

ECpoint ECsystem::pointDecompress(mpz_class compressedPoint){
	//Implement the delta function for decompressing the compressed point
	mpz_class temp=compressedPoint;
	mpz_class br=temp%2;
	if(br==1)
	{
		temp--;
	}
	temp=temp>>1;
	mpz_class z=((temp*temp)%PRIME*temp+(A+PRIME)*temp+B)%PRIME;
	mpz_class root=power(z, (PRIME+1)/4).getValue();
	if((br==1&&root%2==1)||(br==0&&root%2==0))
	{
		ECpoint result(temp,root);
		return result;
	}
	else
	{
		root=PRIME-root;
		ECpoint result(temp,root);
		return result;
	}
}


pair<mpz_class, Zp> ECsystem::encrypt(ECpoint publicKey, mpz_class privateKey,Zp plaintext){
	// You must implement elliptic curve encryption
	//  Do not generate a random key. Use the private key that is passed from the main function
	privateKey%=ORDER;
	ECpoint Q=G*privateKey;	
	ECpoint R=publicKey*privateKey;
	mpz_class C1=pointCompress(Q);
	mpz_class C2=(plaintext.getValue()*pointCompress(R))%PRIME;
	pair<mpz_class, Zp> result;
	result.first=C1;
	result.second=C2;
	return result;
}


Zp ECsystem::decrypt(pair<mpz_class, Zp> ciphertext){
	// Implement EC Decryption
	ECpoint R=pointDecompress(ciphertext.first)*XA;
	Zp temp(pointCompress(R));
	Zp M(ciphertext.second*temp.inverse());
	return M;
}


/*
Sample outputs for incrementVal = 0 or 10.


Public key is: (255327928637822452671873704925306707585883356606885118757,1178994775650364079714920946269118201013822806360569629545)
Enter offset value for sender's private key
0
Encrypted ciphertext is: (9247497218780836794879316060361233346975398346664066655991, 4543832438888944923552833060316220869572984002670167722866)
Original plaintext is: 13144236608967899886525283787315573770527831478534
Decrypted plaintext: 13144236608967899886525283787315573770527831478534
Correct!

Public key is: (255327928637822452671873704925306707585883356606885118757,1178994775650364079714920946269118201013822806360569629545)
Enter offset value for sender's private key
10
Encrypted ciphertext is: (1193511452837154558346198495501062413165085465361676812503, 5128694964446153190876111107899960761864546024068218061320)
Original plaintext is: 13144236608967899886525283787315573770527831478534
Decrypted plaintext: 13144236608967899886525283787315573770527831478534
Correct!


*/
int main(void){
	srand(time(0));
	ECsystem ec;
	mpz_class incrementVal;	
	pair <ECpoint, mpz_class> keys = ec.generateKeys();
	
	
	Zp plaintext = MESSAGE;
	ECpoint publicKey = keys.first;
	cout<<"Public key is: "<<publicKey<<"\n";
	
	cout<<"Enter offset value for sender's private key"<<endl;
	cin>>incrementVal;
	mpz_class privateKey = XB + incrementVal;
	
	pair<mpz_class, Zp> ciphertext = ec.encrypt(publicKey, privateKey, plaintext);	
	cout<<"Encrypted ciphertext is: ("<<ciphertext.first<<", "<<ciphertext.second<<")\n";
	Zp plaintext1 = ec.decrypt(ciphertext);
	
	cout << "Original plaintext is: " << plaintext << endl;
	cout << "Decrypted plaintext: " << plaintext1 << endl;


	if(plaintext == plaintext1)
		cout << "Correct!" << endl;
	else
		cout << "Plaintext different from original plaintext." << endl;	
			
	return 1;

}


