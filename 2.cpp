#include <iostream>
#include <ginac/ginac.h>
#include <unistd.h>
#include <ctime>
using namespace std;
using namespace GiNaC;
#define SDim 9
symbol z1("z1"),z2("z2"),z3("z3"),z4("z4"),z5("z5"),z6("z6"),z7("z7"),z8("z8"),z9("z9");
symbol w1("w1"),w2("w2"),w3("w3"),w4("w4"),w5("w5"),w6("w6"),w7("w7"),w8("w8"),w9("w9");
symbol n1("n1"),n2("n2"),n3("n3"),n4("n4"),n5("n5"),n6("n6"),n7("n7"),n8("n8"),n9("n9");
ex zlist=lst{z1,z2,z3,z4,z5,z6,z7,z8,z9};
ex wlist=lst{w1,w2,w3,w4,w5,w6,w7,w8,w9};
ex nlist=lst{n1,n2,n3,n4,n5,n6,n7,n8,n9};
double timer1,timer2;
int counter;


bool SameIndexQ(int* a,int* b,int indexLen){
    int i;
    for(i=0;i<indexLen;i++){
        if(a[i]!=b[i])return false;
    }
    return true;
} 
//Index Monomial
class IndMon{
public:
    ex coeff=0;
    int index[SDim];
    void set(ex c, int* ind){
        this->coeff=c;
        int i;
        for(i=0;i<SDim;i++)this->index[i]=ind[i];
    }
    //from operator monomial
    void set_from_opmon(ex opMon){
        ex c=opMon;
        int i;
        if(opMon==0){
            this->coeff=0;
            for(i=0;i<SDim;i++)this->index[i]=0;
        }//we think 0 = 0 I[0,0,0,...]
        else{
            int degZ[SDim],degW[SDim];
            for(i=0;i<SDim;i++){
                //If you mistakenly input a polynomial, no warning, but wrong result
                degZ[i]=c.ldegree(zlist[i]);//lowest degree
                degW[i]=c.ldegree(wlist[i]);//lowest degree
                this->index[i]=degZ[i]-degW[i];
                c=c.subs(zlist[i]==1);
                c=c.subs(wlist[i]==1);
            }
            this->coeff=c;
        }
        
    };
    //times a scalar or n-rational ex, on the left
    void times(ex x){
        this->coeff*=x;
    }
    void act_on(IndMon mono){
        ex c=mono.coeff;
        for(int i=0;i<SDim;i++){
            c=c.subs(nlist[i]==nlist[i]+this->index[i]);
            this->index[i]+=mono.index[i];
        }
        this->coeff *= c;
    }
    void act_by(IndMon mono){
        for(int i=0;i<SDim;i++){
            this->coeff = this->coeff.subs(nlist[i]==nlist[i]+mono.index[i]);
            this->index[i]+=mono.index[i];
        }
        this->coeff = (this->coeff)*(mono.coeff);
    }
    void display(){
        if(this->coeff==0){
            cout << "0" << endl;
        }
        else{
            if(this->coeff!=1)cout << "(" << this->coeff << ")*";
            cout << "L[";
            for(int i=0;i<SDim;i++){
                if(i>0)cout<<",";
                cout << this->index[i] ;
            }
            cout << "]" << endl;
        }
    }
    void display(const char* text){
        cout << text;
        (*this).display();
    }
    void inverse(){
        for(int i=0;i<SDim;i++){
            this->coeff=this->coeff.subs(nlist[i]==nlist[i]-this->index[i]);
            this->index[i]*=-1;
        }
        this->coeff=1/(this->coeff);
    }
    void operator=(ex opMon){
        (*this).set_from_opmon(opMon);
    }
};

vector<ex> monomial_list(ex pol){
    int i;
    //check polynomial
    for(i=0;i<SDim;i++){
        if(!(pol.is_polynomial(zlist[i]))){
            cout << "***Error in monomial_list:"<<endl;
            cout << pol << " is not a polynomial in "<<zlist[i]<<endl;
            cout << "Exiting.";
            exit(0);
        }
        if(!(pol.is_polynomial(wlist[i]))){
            cout << "***Error in monomial_list:"<<endl;
            cout << pol << " is not a polynomial in "<<wlist[i]<<endl;
            cout << "Exiting.";
            exit(0);
        }
    }
    vector<ex> monList;
    monList={};
    ex restPol,c,mon;
    restPol=expand(pol);
    int degZ[SDim],degW[SDim];
    while(true){
        if(restPol==0)break;
        c=restPol;
        for(i=0;i<SDim;i++){
            degZ[i]=c.ldegree(zlist[i]);//lowest degree
            c=c.coeff(zlist[i],degZ[i]);
            degW[i]=c.ldegree(wlist[i]);//lowest degree
            c=c.coeff(wlist[i],degW[i]);
        }
        mon=c;
        for(i=0;i<SDim;i++){
            mon=mon*pow(zlist[i],degZ[i]);
            mon=mon*pow(wlist[i],degW[i]);
        }
        restPol=expand(restPol-mon);
        monList.push_back(mon);
    }
    return monList;
}
//the simplification method in collect
ex coeff_simplify(ex coeff){
    ex result;
    clock_t start=clock();
    result=normal(coeff);
    clock_t end=clock();
    double duration = static_cast<double>(end - start) / CLOCKS_PER_SEC;
    timer1+=duration;
    counter+=1;
    return(result);
    //return (normal(coeff));
}

//Index Polynomial
class IndPol{
public:
    vector<IndMon> terms={};
    void set_from_indmon(IndMon mon){
        this -> terms={mon};
    }
    void set_from_opmon(ex opMon){
        IndMon mon;
        mon.set_from_opmon(opMon);
        (*this).set_from_indmon(mon);
        (*this).collect();//Make 0 to be {} not {0*I[0,0,0,0]}
    }
    void set_from_oppol(ex opPol){
        vector<ex> monList;
        monList=monomial_list(opPol);
        ex opMon;
        IndMon mon;
        this->terms={};
        int i;
        for(i=0;i<monList.size();i++){
            opMon=monList[i];
            mon=opMon;//set from op mon
            (this->terms).push_back(mon);
        }
        (*this).collect();
    }
    void add_mon(IndMon mon){
        this->terms.push_back(mon);
    }
    void add(IndPol pol){
        for(int i=0;i<pol.terms.size();i++)this->terms.push_back(pol.terms[i]);
    }
    void display(){
        int n=this->terms.size();
        int i,j;
        ex c;
        if(n==0)cout << "0";
        for(i=0;i<n;i++){
            if(i>0)cout << "+";
            c=this->terms[i].coeff;
            if(c==1){
                cout << "L[";
            }
            else{
                cout << "(" << c << ")*L[";
            }
            
            for(j=0;j<SDim;j++){
                if(j>0)cout <<",";
                cout << this->terms[i].index[j];
            }
            cout << "]";
        }
        cout << endl;
    }
    void display(const char* text){
        cout << text;
        (*this).display();
    }
    void collect(){
        int i,j,n=0;//n is the current term number of result
        int N = this->terms.size();
        bool addedTerm;
        while(true){
            if(n>=N-1)break;//here, N-1, because if only 1 term left, no need to continue
            i=n+1;// manualy "for" loop
            addedTerm=false;
            while(true){
                if(i>=N)break;
                if(SameIndexQ(
                    this->terms[n].index,
                    this->terms[i].index,
                    SDim
                )){
                    this->terms[n].coeff+=
                        this->terms[i].coeff;
                    //this->terms[n].coeff=
                    //   coeff_simplify(this->terms[n].coeff);
                    addedTerm=true;
                    this->terms.erase(this->terms.begin()+i);
                    N--;
                }
                else{
                    i++;
                }
                //if(i==N)break;
            }
            if(addedTerm){
                this->terms[n].coeff=
                    coeff_simplify(this->terms[n].coeff);
            }
            n++;
        }
        //delete 0 terms
        n = this->terms.size();
        i=0;
        while(true){
            if(i>=n)break;
            //this->terms[i].coeff=
            //    coeff_simplify(this->terms[i].coeff);

            //no need to simplify all coeffs, we only need to simplify those changed by adding  terms.
            if(this->terms[i].coeff==0){
                this->terms.erase(this->terms.begin()+i);
                n--;
            }
            else{
                i++;
            }
        }
    }
    //times a scalar or a-rational ex, on the left
    void vanish(){
        this->terms={};
    }
    void times(ex x){
        int i;
        if(x==0)(*this).vanish();
        for(i=0;i<this->terms.size();i++)this->terms[i].times(x);
    }
    void act_on_mon(IndMon mon){
        for(int i=0;i<this->terms.size();i++)this->terms[i].act_on(mon);
    }
    void act_by_mon(IndMon mon){
        for(int i=0;i<this->terms.size();i++)this->terms[i].act_by(mon);
    }
    IndMon cornerize(vector<int> sector){
        int sign[SDim],translation[SDim];
        int i,j;
        for(i=0;i<SDim;i++){
            //translation[i]=0;//no need of this
            sign[i]=sector[i]*2-1;
        }
        for(i=0;i<this->terms.size();i++){
            for(j=0;j<SDim;j++){
                if(i==0){
                    translation[j]=-(this->terms[i].index[j]);
                }
                else{
                    if(
                        sign[j]*((this->terms[i].index[j])+translation[j])<0
                    )translation[j]=-(this->terms[i].index[j]);
                }
            }
            
        }
        IndMon mon;
        mon.coeff=1;
        for(i=0;i<SDim;i++)mon.index[i]=translation[i];
        (*this).act_by_mon(mon);
        return mon;//returning tracked monomial
    }
    void operator=(IndMon mon){
        (*this).set_from_indmon(mon);
    }
    void operator=(ex opPol){
        (*this).set_from_oppol(opPol);
    }

    
};
//x must be n-rational functions free of zlist and wlist
IndMon ind_mon_times(IndMon mon, ex x){
    IndMon result=mon;
    result.times(x);
    return result;
}
IndPol ind_pol_times(IndPol pol, ex x){
    IndPol result=pol;
    result.times(x);
    return result;
}
IndPol ind_pol_add(IndPol pol1, IndPol pol2){
    IndPol result=pol1;
    result.add(pol2);
    result.collect();
    return result;
}
IndPol collected(IndPol pol){
    IndPol result = pol;
    result.collect();
    return result;
}
//Standard index polynomial production
IndPol ind_pol_product(IndPol pol1,IndPol pol2){
    IndPol result,pNew;
    result.vanish();
    for(int i=0;i<pol2.terms.size();i++){
        pNew=pol1;
        pNew.act_on_mon(pol2.terms[i]);
        result.add(pNew);
    }
    result.collect();
    return result;
}

IndPol operator+(IndMon mon1,IndMon mon2){
        IndPol result;
        result.set_from_indmon(mon1);
        result.add_mon(mon2);
        result.collect();
        return result;
}
IndPol operator+(IndPol pol,IndMon mon){
        IndPol result=pol;
        result.add_mon(mon);
        result.collect();
        return result;
}
IndPol operator+(IndMon mon,IndPol pol){
        IndPol result;
        result.set_from_indmon(mon);
        result.add(pol);
        result.collect();
        return result;
}
IndPol operator+(IndPol pol1,IndPol pol2){
        return ind_pol_add(pol1,pol2);
}
IndPol operator+(IndPol pol,ex x){
        IndMon monx;
        monx=x;
        return pol+monx;
}
IndPol operator+(ex x,IndPol pol){
        IndMon monx;
        monx=x;
        return monx+pol;
}
IndPol operator+(IndMon mon,ex x){
        IndMon monx;
        monx=x;
        return mon+monx;
}
IndPol operator+(ex x,IndMon mon){
        IndMon monx;
        monx=x;
        return monx+mon;
}
IndPol operator-(IndMon mon1,IndMon mon2){
        IndPol result;
        result.set_from_indmon(mon1);
        result.add_mon(ind_mon_times(mon2,-1));
        result.collect();
        return result;
}
IndPol operator-(IndPol pol,IndMon mon){
        IndPol result=pol;
        result.add_mon(ind_mon_times(mon,-1));
        result.collect();
        return result;
}
IndPol operator-(IndMon mon,IndPol pol){
        IndPol result;
        result.set_from_indmon(mon);
        result.add(ind_pol_times(pol,-1));
        result.collect();
        return result;
}
IndPol operator-(IndPol pol1,IndPol pol2){
        return ind_pol_add(pol1,ind_pol_times(pol2,-1));
}
IndPol operator-(IndPol pol,ex x){
        IndMon monx;
        monx=x;
        return pol-monx;
}
IndPol operator-(ex x,IndPol pol){
        IndMon monx;
        monx=x;
        return monx-pol;
}
IndPol operator-(IndMon mon,ex x){
        IndMon monx;
        monx=x;
        return mon-monx;
}
IndPol operator-(ex x,IndMon mon){
        IndMon monx;
        monx=x;
        return monx-mon;
}
IndMon operator*(IndMon mon,ex x){
    return ind_mon_times(mon,x);
}
IndMon operator*(ex x,IndMon mon){
    return ind_mon_times(mon,x);
}
IndPol operator*(IndPol pol,ex x){
    return ind_pol_times(pol,x);
}
IndPol operator*(ex x,IndPol pol){
    return ind_pol_times(pol,x);
}
IndMon operator*(IndMon mon1,IndMon mon2){
    IndMon result=mon1;
    result.act_on(mon2);
    return result;
}
IndPol operator*(IndMon mon,IndPol pol){
    IndPol result=pol;
    result.act_by_mon(mon);
    return result;
}
IndPol operator*(IndPol pol,IndMon mon){
    IndPol result=pol;
    result.act_on_mon(mon);
    return result;
}
IndPol operator*(IndPol pol1,IndPol pol2){
        return ind_pol_product(pol1,pol2);
}
IndMon operator/(ex x, IndMon mon){
    IndMon result=mon;
    result.inverse();
    return x*result;
}
//well, shall we define left-division or right-division?
//here, it is right-division.
IndMon operator/(IndMon mon1, IndMon mon2){
    IndMon result=mon2;
    result.inverse();
    return mon1*result;
}
IndPol operator/(IndPol pol, IndMon mon){
    IndMon result=mon;
    result.inverse();
    return pol*result;
}
IndPol operator/(IndPol pol, ex x){
    return ind_pol_times(pol,1/x);
}
IndMon operator/(IndMon mon, ex x){
    return ind_mon_times(mon,1/x);
}
bool operator==(IndMon mon1,IndMon mon2){
    IndPol pold;
    pold=mon1-mon2;
    if(pold.terms.size()==0){
        return true;
    }
    else{
        return false;
    }
}
bool operator==(IndMon mon,IndPol pol){
    IndPol pold;
    pold=mon-pol;
    if(pold.terms.size()==0){
        return true;
    }
    else{
        return false;
    }
}
bool operator==(IndPol pol,IndMon mon){
    IndPol pold;
    pold=pol-mon;
    if(pold.terms.size()==0){
        return true;
    }
    else{
        return false;
    }
}
bool operator==(IndPol pol1,IndPol pol2){
    IndPol pold;
    pold=pol1-pol2;
    if(pold.terms.size()==0){
        return true;
    }
    else{
        return false;
    }
}
bool operator==(IndMon mon,ex x){
    IndPol pold;
    pold=mon-x;
    if(pold.terms.size()==0){
        return true;
    }
    else{
        return false;
    }

}
bool operator==(ex x,IndMon mon){
    IndPol pold;
    pold=x-mon;
    if(pold.terms.size()==0){
        return true;
    }
    else{
        return false;
    }

}
bool operator==(IndPol pol,ex x){
    IndPol pold;
    pold=pol-x;
    if(pold.terms.size()==0){
        return true;
    }
    else{
        return false;
    }

}
bool operator==(ex x,IndPol pol){
    IndPol pold;
    pold=x-pol;
    if(pold.terms.size()==0){
        return true;
    }
    else{
        return false;
    }

}
bool operator!=(IndMon mon1,IndMon mon2){
    IndPol pold;
    pold=mon1-mon2;
    if(pold.terms.size()>0){
        return true;
    }
    else{
        return false;
    }
}
bool operator!=(IndMon mon,IndPol pol){
    IndPol pold;
    pold=mon-pol;
    if(pold.terms.size()>0){
        return true;
    }
    else{
        return false;
    }
}
bool operator!=(IndPol pol,IndMon mon){
    IndPol pold;
    pold=pol-mon;
    if(pold.terms.size()>0){
        return true;
    }
    else{
        return false;
    }
}
bool operator!=(IndPol pol1,IndPol pol2){
    IndPol pold;
    pold=pol1-pol2;
    if(pold.terms.size()>0){
        return true;
    }
    else{
        return false;
    }
}
bool operator!=(IndMon mon,ex x){
    IndPol pold;
    pold=mon-x;
    if(pold.terms.size()>0){
        return true;
    }
    else{
        return false;
    }

}
bool operator!=(ex x,IndMon mon){
    IndPol pold;
    pold=x-mon;
    if(pold.terms.size()>0){
        return true;
    }
    else{
        return false;
    }

}
bool operator!=(IndPol pol,ex x){
    IndPol pold;
    pold=pol-x;
    if(pold.terms.size()>0){
        return true;
    }
    else{
        return false;
    }

}
bool operator!=(ex x,IndPol pol){
    IndPol pold;
    pold=x-pol;
    if(pold.terms.size()>0){
        return true;
    }
    else{
        return false;
    }

}
//cornerize:
// to be left acted by a mon, let the result:
// 1. all mons in given sector
// 2. the most close to the corner 
// example: z1^3*w2 + z1^2*z2, cornerize in sector {1,1}, resulting in z1+z2
// BE CAREFUL, the "sector" concept is sightly different to that in Feynman integrals
// I[0,0,0,0] is in sector {0,0,0,0} in Feynman integral context
// but here, it is in all sectors
// similarly, I[1,1,-1,0] is in both sectors {1,1,0,1} and {1,1,0,0}
IndPol cornerized(IndPol pol, vector<int> sector){
    IndPol result;
    result.cornerize(sector);
    return result;
}
vector<IndPol> trancked_conerized(IndPol pol, vector<int> sector){
    vector<IndPol> result;
    result={};
    IndPol polCornerized,polTracked;
    polCornerized=pol;
    polTracked=(polCornerized.cornerize(sector));
    result={polTracked,polCornerized};
    //polTracked=pol/polCornerized;
}
// CAUTION again, the concept of a sector is slightly modified.
bool ind_mon_in_sector_q(IndMon mon,vector<int> sector){
    int i;
    for(i=0;i<SDim;i++){
        if(
            (2*sector[i]-1)*(mon.index[i])<0//see here, index==0 is in sector.
        )return false;
    }
    return true;
}
// As a concequence of the sector concept redef,
// if mon1==mon2, they are divisible to each other
// this is consistent with our habit
bool ind_mon_divisible_q(IndMon mon1, IndMon mon2, vector<int> sector){
    int i;
    for(i=0;i<SDim;i++){
        if(
            (2*sector[i]-1)*(mon1.index[i]-mon2.index[i])<0//see here, index==0 is in sector.
        )return false;
    }
    return true;
}
vector<vector<int>> monomial_ordering_matrix(vector<int> sector, const char* orderingString)
{
    //to be finished
    vector<vector<int>> m={};
    vector<int> row;
    char ordering[1024];
    strcpy(ordering,orderingString);
    int n=sector.size();
    int i,j;
    bool unidentifiedOrdering=true;
    if(strcmp(ordering,"lexicographic")==0){
        unidentifiedOrdering=false;
        for(i=0;i<n;i++){
            row={};
            for(j=0;j<n;j++){
                if(i==j){
                    row.push_back(1);
                }
                else{
                    row.push_back(0);
                }
            }
            m.push_back(row);
        }
        
        
    }
    if(strcmp(ordering,"degree_lexicographic")==0){
        unidentifiedOrdering=false;
        for(i=0;i<n;i++){
            row={};
            for(j=0;j<n;j++){
                if(i==0||i-1==j){
                    row.push_back(1);
                }
                else{
                    row.push_back(0);
                }
            }
            m.push_back(row);
        }
        
    }
    if(strcmp(ordering,"degree_reverse_lexicographic")==0){
        unidentifiedOrdering=false;
        for(i=0;i<n;i++){
            row={};
            for(j=0;j<n;j++){
                if(i+j<n){
                    row.push_back(1);
                }
                else{
                    row.push_back(0);
                }
            }
            m.push_back(row);
        }
        
    }
    for(i=0;i<n;i++){
        if(sector[i]==0){
            for(j=0;j<n;j++){
                m[j][i]*=-1;//not m[i,j]
            }
        }
    }
    if(unidentifiedOrdering){
        cout <<"*** Error in monomial_ordering_matrix:"<<endl;
        
        cout <<"ordering string \""<<orderingString<<"\" is unidentified."<<endl;
        cout << "Exit."<<endl;
        exit(0);
    }
    return m;

}
void matrix_display(vector<vector<int>> m){
    int i,j;
    for(i=0;i<m.size();i++){
        for(j=0;j<m[i].size();j++){
            if(j>0)cout<<"\t";
            cout << m[i][j];
        }
        cout <<endl;
    }
}
vector<int> index_order(int* ind, vector<vector<int>> monomialOrderingMatrix){
    vector<int> result={};
    int i,j,n,order;
    n=monomialOrderingMatrix.size();
    for(i=0;i<n;i++){
        order=0;
        for(j=0;j<n;j++){
            order+=monomialOrderingMatrix[i][j]*ind[j];
            //cout<<"order("<<i<<","<<j<<")="<<order<<endl;
        }
        result.push_back(order);
    }
    return result;
}
int index_order_sign(vector<int> order){
    int i;
    for(i=0;i<order.size();i++){
        if(order[i]>0)return 1;
        if(order[i]<0)return -1;
    }
    return 0;
}

int ind_mon_compare(
    IndMon mon1,IndMon mon2,
    vector<int> sector,
    const char* orderingString
){
    //returns 1 if mon1 is higher ordered, 
    //-1 the reverse, 0 if the two same ordered
    int indexDiff[SDim];
    int i;
    for(int i=0;i<SDim;i++){
        indexDiff[i]=mon1.index[i]-mon2.index[i];
    }
    vector<vector<int>> monomialOrderingMatrix;
    monomialOrderingMatrix=monomial_ordering_matrix(sector,orderingString);
    vector<int> diffOrder=index_order(indexDiff,monomialOrderingMatrix);
    return index_order_sign(diffOrder);
}

IndMon leading_term(
    IndPol pol, 
    vector<int> sector, 
    const char* orderingString
){
    int i;
    ex coeff_LT=0;
    IndMon leadingMon;
    //we donot care its coeff, the coeff is stored in coeff_LT
    //this is a consideration of data structure,
    //that "+" of 2 IndMons gives a IndPol
    //even it has only 1 term.
    for(i=0;i<pol.terms.size();i++){
        if(i==0){
            leadingMon=pol.terms[i];
            coeff_LT=pol.terms[i].coeff;
        }
        else{
            
            switch(ind_mon_compare(
                leadingMon,
                pol.terms[i],
                sector,
                orderingString
            )){
                case 1:
                    //do nothing here
                    break;
                case 0:
                    coeff_LT+=pol.terms[i].coeff;
                    break;
                case -1:
                    leadingMon=pol.terms[i];
                    coeff_LT=pol.terms[i].coeff;
                    break;
            }
        }
        //leadingMon.display("leadingMon=");
    }
    leadingMon.coeff=coeff_LT;
    return leadingMon;
}


class IndPolDivisionResult{
public:
    IndPol quotient;
    IndPol remainder;
};
//left-division: F/g->F=q g+r
IndPolDivisionResult ind_pol_division(
    IndPol pol1,IndPol pol2,vector<int> sector,const char* orderingString
){
    IndPolDivisionResult result;
    IndPol rest;
    rest=pol1;
    result.remainder=0;
    result.quotient=0;
    IndMon pol2LT,restLT,q1;
    pol2LT=leading_term(pol2,sector,orderingString);
    while(true){
        if(rest==0)break;
        restLT=leading_term(rest,sector,orderingString);
        if((ind_mon_divisible_q(restLT,pol2LT,sector))){
            q1=restLT/pol2LT;//Do we need to cornerize?
            //I think in this function, no , no cornerize
            //also take care the left and right 
            // q1 cant be (1/poly2LT)*remainderLT
            //(q1*pol2).display("q1*pol2=");
            rest=rest-q1*pol2;
            result.quotient=result.quotient+q1;
        }
        else{
            //restLT.display("restLT=");
            rest=rest-restLT;
            result.remainder=result.remainder+restLT;
        }
        //rest.display("rest=");
        //restLT.display("restLT=");
        //sleep(1);
        
    }
    return result;
}
IndPolDivisionResult ind_pol_division(
    IndPol pol1,IndMon mon,vector<int> sector,const char* orderingString
){
    IndPol pol2;
    pol2=mon;
    return ind_pol_division(pol1,pol2,sector,orderingString);
}
IndPolDivisionResult ind_pol_division(
    IndPol pol1,ex x,vector<int> sector,const char* orderingString
){
    IndPol pol2;
    pol2=x;
    return ind_pol_division(pol1,pol2,sector,orderingString);
}


//it says... be careful with 0?
IndMon ind_mon_lcm(IndMon mon1,IndMon mon2,vector<int>sector){
    IndMon result;
    //result=0;//some initialization which seems to be unnecessary
    int i;
    for(i=0;i<SDim;i++){
        if(
            (2*sector[i]-1)*(mon1.index[i]-mon2.index[i])>0
        ){
            result.index[i]=mon1.index[i];
        }
        else{
            result.index[i]=mon2.index[i];
        }
    }
    result.coeff=1;
    //the rest part is refining the coeff
    //It says that this is for the efficiency of the algorithm 
    //but I forgot why this will result in a higher efficiency
    //may be following the 2 criterion:
    //1. no denominator(in coeff) in the compensate coeff while reaching the lcm
    //2. the compensate coeff should be as lower ordered as possible
    IndMon precompensateMon1,precompensateMon2;
    for(i=0;i<SDim;i++){
        precompensateMon1.index[i]=result.index[i]-mon1.index[i];
        precompensateMon2.index[i]=result.index[i]-mon2.index[i]; 
    }
    precompensateMon1.coeff=1;
    precompensateMon2.coeff=1;
    IndMon prelcm1,prelcm2;
    prelcm1=precompensateMon1*mon1;
    prelcm2=precompensateMon2*mon2;
    ex prelcmCoeff1,prelcmCoeff2;
    prelcmCoeff1=prelcm1.coeff;
    prelcmCoeff2=prelcm2.coeff;
    ex numden1,numden2,num1,num2,den1,den2;
    numden1=numer_denom(prelcmCoeff1);
    numden2=numer_denom(prelcmCoeff2);
    num1=numden1[0];
    den1=numden1[1];
    num2=numden2[0];
    den2=numden2[1];
    result.coeff=lcm(num1,num2)/gcd(den1,den2);
    return result;
}

IndPol ind_pol_spair(IndPol pol1,IndPol pol2, vector<int> sector,const char* orderingString){
    IndMon lt1,lt2,lcm,q1,q2;
    lt1=leading_term(pol1,sector,orderingString);
    lt2=leading_term(pol2,sector,orderingString);
    lcm=ind_mon_lcm(lt1,lt2,sector);
    q1=lcm/lt1;
    q2=lcm/lt2;
    return q1*pol1-q2*pol2;
}
vector<IndPol> tracked_ind_pol_spair(IndPol pol1,IndPol pol2, vector<int> sector,const char* orderingString){
    IndMon lt1,lt2,lcm,q1,q2;
    lt1=leading_term(pol1,sector,orderingString);
    lt2=leading_term(pol2,sector,orderingString);
    lcm=ind_mon_lcm(lt1,lt2,sector);
    q1=lcm/lt1;
    q2=lcm/lt2;
    return {q1*pol1-q2*pol2,q1+0,q2+0};
}

class IndPolSetDivisionResult{
public:
    vector<IndPol> quotients={};
    IndPol remainder;
void display(){
    int n=this->quotients.size();
    int i;
    cout<<"qs:"<<endl;
    for(i=0;i<n;i++){
        cout<<"\tq["<<i<<"]=";
        this->quotients[i].display();
    }
    this->remainder.display("r=");
}
void display(const char* str){
    cout<<str;
    (*this).display();
}
};
IndPolSetDivisionResult ind_pol_set_division(
    IndPol pol,vector<IndPol> polList,vector<int> sector,const char* orderingString
){
    IndPol zeroPol;
    zeroPol=0;
    IndPolSetDivisionResult result;
    
    result.remainder=pol;
    result.quotients={};
    int i;
    int polListLen=polList.size();
    if(polListLen==0)return result;//special input
    for(i=0;i<polListLen;i++){
        result.quotients.push_back(zeroPol);
    }
    //ini finished here
    i=0;
    int n=0;// n counts for how many times did the division do nothing
    IndPolDivisionResult divisionResult1;
    IndPol q,newRemainder;
    while(true){
        newRemainder=result.remainder;//I do not know why we need this
        
        divisionResult1=ind_pol_division(newRemainder,polList[i],sector,orderingString);
        
        q=divisionResult1.quotient;
        newRemainder=divisionResult1.remainder;
        
        if(q!=0){
            result.remainder=newRemainder;
            result.quotients[i]=result.quotients[i]+q;//I added this line
            //to return the quotients
            //I do not know why in the mma version I did not write this line
            n=0;
        }
        else{
            n++;
        }
        if(n==polListLen)break;
        i++;
        if(i>=polListLen)i-=polListLen;//loop
    }
    return result;
}

void ind_pol_set_display(vector<IndPol> pols){
    int i;
    for(i=0;i<pols.size();i++){
        cout<<"\t_["<<i<<"]:";
        pols[i].display();
    }
}
void ind_pol_set_display(vector<IndPol> pols,const char* str){
    cout<<str<<endl;
    ind_pol_set_display(pols);
}
class GBResult{
public:
    vector<IndPol> basis={};
    vector<vector<IndPol>> transformationMatrix={}; 
};
class GBOptions{
public:
    bool progress_indicator=false;
    bool tracking=false;
};
void check_GB(
    vector<IndPol> polList,
    vector<IndPol> blist,
    vector<vector<IndPol>> transformation,
    const char* label){
    int i,j;
    IndPol checking;
    cout<<label<<": {";
    for(i=0;i<blist.size();i++){
        checking=blist[i];
        for(j=0;j<polList.size();j++){
            checking=checking-transformation[i][j]*polList[j];
        }
        if(checking==0){
            cout<<0;
        }
        else{
            cout<<1;
        }
        if(i<blist.size()-1)cout<<",";
    }
    cout<<"}"<<endl;
}
GBOptions GB_DEFAULT_SETTINGS;
GBResult ind_pol_Buchberger(vector<IndPol> polList,vector<int> sector, const char *orderingString,GBOptions settings){
    GBResult result;
    vector<vector<IndPol>> queue;
    vector<IndPol> blist,pair;
    IndPol sPol,r;
    IndPolSetDivisionResult divisionResult;
    int i,j;
    vector<vector<IndPol>> transformation;
    vector<vector<vector<IndPol>>> queueT;
    vector<IndPol> polsTmp;
    IndPol polTmp;
    IndMon cornerizeTrackTmp;
    transformation={};
    blist={};
    for(i=0;i<polList.size();i++){
        if(polList[i]!=0)blist.push_back(polList[i]);//dezeroize;
        if((settings.tracking)&&(polList[i]!=0)){
            polsTmp={};
            for(j=0;j<polList.size();j++){
                if(i==j){
                    polTmp=1;
                }
                else{
                    polTmp=0;
                }
                polsTmp.push_back(polTmp);
            }
            transformation.push_back(polsTmp);
        }
    }
    for(i=0;i<blist.size();i++){//cornerization!
        if(settings.tracking){
            cornerizeTrackTmp=(blist[i].cornerize(sector));
            for(j=0;j<polList.size();j++){
                transformation[i][j]=cornerizeTrackTmp*transformation[i][j];
            }
        }
        else{
            blist[i].cornerize(sector);
        }
        
    }
    if(blist.size()<2){
        result.basis=blist;
        if(settings.tracking)result.transformationMatrix=transformation;
        return result;
    }//no need to continue;
    queue={};
    queueT={};
    for(i=0;i<blist.size()-1/*this is because we leave position for j*/;i++){
        for(j=i+1;j<blist.size();j++){
            queue.push_back({blist[i],blist[j]});
            if(settings.tracking){
                queueT.push_back({transformation[i],transformation[j]});
            }
        }
    }
    
    vector<IndPol> trackedSpairTmp,rT,qs;//T means tracked or transform
    IndPol q1,q2;
    //IndPol tmp1,tmp2,tmp3;//debug
    //vector<IndPol> tmplist;//debug
    //vector<vector<IndPol>> tmpMat;//debug
    vector<vector<IndPol>> pairT;
    while(queue.size()>0){
        pair=queue[0];
        if(settings.tracking)pairT=queueT[0];
        if(settings.tracking){
            trackedSpairTmp=tracked_ind_pol_spair(pair[0],pair[1],sector,orderingString);
            sPol=trackedSpairTmp[0];
        }
        else{
            sPol=ind_pol_spair(pair[0],pair[1],sector,orderingString);
        }
        divisionResult=ind_pol_set_division(sPol,blist,sector,orderingString);
        r=divisionResult.remainder;
        r.collect();//although collected, shall r be simplified? 
        //because, some "zero" coefficients might not be written as "0"
        //this also needs to be concerned in ind pol divisions
        
        if(settings.tracking){
            cornerizeTrackTmp=(r.cornerize(sector));
            //returns the monomial used to cornerize,
            //at the same time cornerize r
        }
        else{
            r.cornerize(sector);
        }
        if(r!=0){
            for(i=0;i<blist.size();i++){
                queue.push_back({blist[i],r});
            }
            if(settings.tracking){
                rT={};
                q1=trackedSpairTmp[1];
                q2=trackedSpairTmp[2];
                for(i=0;i<polList.size();i++){
                    rT.push_back(q1*pairT[0][i]-q2*pairT[1][i]);
                }//track s pair
                qs=divisionResult.quotients;
                for(j=0;j<blist.size();j++){
                    for(i=0;i<polList.size();i++){
                        rT[i]=rT[i]-qs[j]*transformation[j][i];
                    }
                }//track division
                for(i=0;i<polList.size();i++){
                    rT[i]=cornerizeTrackTmp*rT[i];
                }//track cornerization
                for(i=0;i<blist.size();i++){
                    queueT.push_back({transformation[i],rT});
                }
                transformation.push_back(rT);
            }
            blist.push_back(r);
            //ind_pol_set_display(blist,"blist:");
        }
        queue.erase(queue.begin());
        if(settings.tracking)queueT.erase(queueT.begin());
        if(settings.progress_indicator)cout<<"("<<queue.size()<<")"<<endl;
        //ind_pol_set_display(blist,"blist:");
    }
    result.basis=blist;
    if(settings.tracking)result.transformationMatrix=transformation;
    return result;
}
GBResult ind_pol_GB(vector<IndPol> polList,vector<int> sector, const char *orderingString,GBOptions settings){
    GBResult result;
    vector<IndPol> blist,divisors,quotientsTmp;
    vector<vector<IndPol>> transformation;
    IndPol r;
    IndPolSetDivisionResult divisionResult;
    result=ind_pol_Buchberger(polList,sector,orderingString,settings);
    blist=result.basis;
    if(settings.tracking)transformation=result.transformationMatrix;
    int i=0,n=0,j,k;//n: how may times that the division changes nothing
    while(true){
        if(blist.size()<2)break;
        if(i>=blist.size())i-=blist.size();//loop
        divisors=blist;
        divisors.erase(divisors.begin()+i);//do not divide by itself
        divisionResult=ind_pol_set_division(blist[i],divisors,sector,orderingString);
        r=divisionResult.remainder;
        r.collect();
        r.cornerize(sector);
        if(r==0){//if so, no i++
            blist=divisors;
            if(settings.tracking){
                transformation.erase(transformation.begin()+i);
            }   
            n=0;
        }
        else{
            //cout<<"f21,i="<<i<<endl;
            
            if(r==blist[i]){
                n++;//nothing changes,n+=1
            }
            else{
                blist[i]=r;
                if(settings.tracking){
                    quotientsTmp=divisionResult.quotients;
                    for(j=0;j<blist.size();j++){
                        for(k=0;k<polList.size();k++){
                            if(j!=i){
                                if(j<i){
                                    transformation[i][k]=
                                        transformation[i][k]-
                                        quotientsTmp[j]*transformation[j][k];
                                }
                                else{
                                    transformation[i][k]=
                                        transformation[i][k]-
                                        quotientsTmp[j-1]*transformation[j][k];
                                }
                            }//else do nothing
                        }
                    }
                }
                n=0;
            }
            i++;
        }
        if(n>=blist.size())break;
        if(settings.progress_indicator)cout<<"["<<blist.size()<<"]"<<endl;
        //ind_pol_set_display(blist,"blist:");
    }
    //if(GB_PROGRESS_INDICATOR)cout<<endl;
    ex c;
    IndMon lt;
    for(i=0;i<blist.size();i++){
        lt=leading_term(blist[i],sector,orderingString);
        c=lt.coeff;
        blist[i]=blist[i]/c;
        if(settings.tracking){
            for(j=0;j<polList.size();j++){
                transformation[i][j]=transformation[i][j]/c;
            }
        }
    }
    result.basis=blist;
    if(settings.tracking)result.transformationMatrix=transformation;
    return result;
}
GBResult ind_pol_GB(vector<IndPol> polList,vector<int> sector, const char *orderingString){
    return ind_pol_GB(polList,sector,orderingString,GB_DEFAULT_SETTINGS);
}
class IndPolIdeal{
public:
    vector<IndPol> gens={};
void display(){
    ind_pol_set_display(this->gens);
}
void display(const char* str){
    ind_pol_set_display(this->gens,str);
}
void operator=(vector<IndPol> pols){
    this->gens=pols;
}
void operator=(vector<ex> opPols){
    this->gens={};
    IndPol pol;
    int i;
    for(i=0;i<opPols.size();i++){
        pol=opPols[i];
        (this->gens).push_back(pol);
    }
}
void operator=(GBResult result){
    this->gens=result.basis;
}
};
IndPolSetDivisionResult ind_pol_set_division(
    IndPol pol,IndPolIdeal ideal,vector<int> sector,const char* orderingString
){
    return ind_pol_set_division(pol,ideal.gens,sector,orderingString);
}
GBResult ind_pol_GB(IndPolIdeal ideal,vector<int> sector, const char *orderingString,GBOptions settings){
    return ind_pol_GB(ideal.gens,sector,orderingString,settings);   
}
GBResult ind_pol_GB(IndPolIdeal ideal,vector<int> sector, const char *orderingString){
    return ind_pol_GB(ideal.gens,sector,orderingString);
}

int main()
{   
    GB_DEFAULT_SETTINGS.progress_indicator=true;
    GB_DEFAULT_SETTINGS.tracking=true;
    IndMon m1,m2,m3;
    symbol s("s"),d("d"),t("t"),mm("mm");
    IndPol pol;
    vector<int> sector={1,1,1,1,1,1,1,1,1};
    pol=w3*(w1+w2);
    pol.display("pol=");
    (pol.cornerize(sector)).display("ctrack=");
    pol.display("pol=");
    vector<ex> ibpVectors;
    ibpVectors={
        2*(-1 + n2)*(4*mm - s)*s - 2*(-1 + n2)*(mm - s)*w1 + (2*mm - 2*mm*n1 - 5*s - 2*d*s + 3*n1*s + 4*n2*s)*w2 + (1 - d + n1)*w1*w2 + (3 + 2*d - 3*n1 - 2*n2)*pow(w2,2),
         (-1 + n2)*(4*mm - s)*s + (-1 + n2)*s*w1 - (2 + d - n1 - 2*n2)*s*w2 + (-1 - d + n1 + n2)*w1*w2 + (1 + d - n1 - n2)*pow(w2,2),
        -((-1 + n1)*(4*mm - s)*s) + (2*mm - 2*mm*n2 + s + d*s - 2*n1*s)*w1 + (-d + n1)*pow(w1,2) - (-1 + n1)*(2*mm + s)*w2 + (4 + 2*d - 3*n1 - 2*n2)*w1*w2,
        -((-1 + n1)*(4*mm - s)*s) + (2 + d - 2*n1 - n2)*s*w1 + (-1 - d + n1 + n2)*pow(w1,2) - (-1 + n1)*s*w2 + (1 + d - n1 - n2)*w1*w2
    };
    ibpVectors={-1 - z1 + z4, -1 - z2 + z5, -1 - z2 - z1*z2 + z6, -1 - z3 + z7, -1 - z3 - z2*z3 + z8, -1 - z3 - z2*z3 - z1*z2*z3 + z9, n1*w1 + n4*w4 + n6*w6*z2 + n9*w9*z2*z3, n2*w2 + n5*w5 + n6*w6*(1 + z1) + n8*w8*z3 + n9*w9*(z3 + z1*z3), n3*w3 + n7*w7 + n8*w8*(1 + z2) + n9*w9*(1 + z2 + z1*z2)};
    IndPolIdeal ibps,gb;
    ibps=ibpVectors;
    ibps.display("ibps=");
    GBResult gbResult;
    int i;
    //gb.gens={};
    for(i=0;i<ibps.gens.size();i++){
        break;
        cout<<"=====<"<<i<<">====="<<endl;
        gb.gens.push_back(ibps.gens[i]);
        if(i==0)continue;
        gbResult=ind_pol_GB(gb,sector,"degree_reverse_lexicographic");
        gb=gbResult;
    }
    timer1=0,timer2=0,counter=0;
    clock_t start=clock();
    gbResult=ind_pol_GB(ibps,sector,"degree_reverse_lexicographic");
    clock_t end=clock();
    double duration = static_cast<double>(end - start) / CLOCKS_PER_SEC;
    timer2+=duration;
    gb=gbResult;
    gb.display("GB:"); 
    
    cout<<"counter="<<counter<<endl;
    cout<<"timer1="<<timer1<<endl;
    cout<<"timer2="<<timer2<<endl;
    
    IndPolIdeal ideal;
    //gbResult=ind_pol_GB(ibps,sector,"degree_reverse_lexicographic");
    //gb=gbResult;
    
    //pol=z6-1;
    //leading_term(pol,sector,"degree_reverse_lexicographic").display();
    //f=(z1*z1-1)/(1+z1)+0*z2/(1+z4);
    //cout<<f<<endl;
    //cout<<normal(f)<<endl;
    //vector<vector<IndPol>> transformation;
    //transformation=gbResult.transformationMatrix;
    //IndPol checking;
    //checking=0;
    //for(i=0;i<transformation.size();i++){
    //    checking=checking+(transformation[0][i]*ibps.gens[i]);
    //}
    //checking.display("checking=");
    //ibpVectors={
    //    n1 - n2 + n1*s*z1 - n1*w2*z1 - n2*s*z2 + n2*w1*z2, 
    //    d - 2*n1 - n2 - 2*mm*n1*z1 + (-2*mm*n2 + n2*s)*z2 - n2*w1*z2
   // };
    //ibpVectors={};
    
    //gb=ind_pol_GB(ibps,sector,"degree_reverse_lexicographic");
    //gb.display("GB:");
    //m1=z1*z1*z2*w4*w3*n2*n4*s;
    //m2=n1*n2*n3*n4*pow(z1,4)*z2*z3*t;
    //m3=z1*w1*w2*z3*w4*(n1+n2)*d;
    //cout << "m1=";m1.display();
    //cout << "m2=";m2.display();
    //cout << "m3=";m3.display();
    //(1/m1).display("1/m1=");
    //((1/m1)*m1).display("(1/m1)*m1=");
   // (m1*(1/m1)).display("m1*(1/m1)=");
    //IndPol pol=m1+m2+m3;
    //pol.collect();
    //pol.display("m1+m2+m3=");
   // (m1*m2).display("m1*m2=");
   // (m2*m1).display("m2*m1=");
   // (pol/m2).display("pol/m2=");
   // ((1/m2)*pol).display("(1/m2)*pol=");

    
    //vector<vector<int>> mom=monomial_ordering_matrix(sector,
    //    "degree_reverse_lexicographic"
    //);
    //IndMon lt=leading_term(pol,sector,"degree_reverse_lexicographic");
    //cout<<ind_mon_compare(m1,m2,sector,"degree_reverse_lexicographic")<<endl;
    //lt.display();
    //matrix_display(mom);
    //IndPolDivisionResult qr;
    //qr=ind_pol_division(pol,m1,sector,"degree_reverse_lexicographic");
    //pol.display("pol=");
    //IndPolSetDivisionResult qsr;
    //qsr=ind_pol_set_division(pol+1,{m1+0,m2+0,m3+0},sector,"degree_reverse_lexicographic");
    //qsr.display();  
    return 0;
}