#include <iostream>
#include <ginac/ginac.h>
using namespace std;
using namespace GiNaC;
#define SDim 4
struct index_monomial{
    ex coeff;
    int index[SDim];   
};
struct index_polynomial{
    index_monomial* terms=NULL;
    int termNumber;
};
bool SameIndexQ(int* a,int* b,int indexLen){
    int i;
    for(i=0;i<indexLen;i++){
        if(a[i]!=b[i])return false;
    }
    return true;
} 
index_polynomial IPCollect(index_polynomial indPoly){
    int i,j,n=0;//n is the term number of result
    int N = indPoly.termNumber;
    index_polynomial result;
    result.terms=
        (index_monomial* )malloc(N*sizeof(index_monomial));
    result.termNumber=N;
    bool sameTermQ;
    bool sameTermPosition;
    for(i=0;i<indPoly.termNumber;i++){
        bool sameIndexQ=false;
        for(j=0;j<n;j++){
            if(SameIndexQ(
                (indPoly.terms)[i].index,
                (result.terms)[j].index,
                SDim
            )){
                sameIndexQ=true;
                sameTermPosition=j;
                break;
            }
        }
        if(sameIndexQ){
            result.terms[sameTermPosition].coeff
                +=indPoly.terms[i].coeff;
        }
        else{
            result.terms[n]=indPoly.terms[i];
            n++;
        }
    }
    index_polynomial result1;
    result1.terms=
        (index_monomial* )malloc(n*sizeof(index_monomial));
    result1.termNumber=n;
    for(i=0;i<n;i++)result1.terms[i]=result.terms[i];
    free(result.terms);
    return result1;
}
void IPDisplay(index_polynomial indPoly){
    int j;
    for(int i=0;i<indPoly.termNumber;i++){
        if(i>0)cout << "+";
        cout << "(" << indPoly.terms[i].coeff << ")I[";
        for(j=0;j<SDim;i++)cout << indPoly.terms[i].index[j];
        cout << "]";
    }
}
int main()
{   
    symbol z1("z1"),z2("z2"),z3("z3"),z4("z4");
    symbol w1("w1"),w2("w2"),w3("w3"),w4("w4");
    symbol a1("a1"),a2("a2"),a3("a3"),a4("a4");
    ex zs=lst{z1,z2,z3,z4};
    ex ws=lst{w1,w2,w3,w4};
    ex as=lst{a1,a2,a3,a4};
    index_monomial m1,m2;
    int i;
    m1.coeff=a1;
    for(i=0;i<4;i++){
        m1.index[i]=i;
    }
    index_polynomial poly;
    
    poly.terms=(index_monomial* )malloc(2*sizeof(index_monomial));
    poly.termNumber=2;
    /*
    poly.terms[0]=m1;
    poly.terms[1]=m1;
     */
    m2=m1;
    
    index_monomial* mp2=(poly.terms);
    
    //m2=mp2[0];
    cout << "??" << endl;
    cout << (mp2[1].coeff) << endl;
    return 0;
}