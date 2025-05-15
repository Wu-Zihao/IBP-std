#include <iostream>
#include <ginac/ginac.h>
using namespace std;
using namespace GiNaC;
#define SDim 4
symbol z1("z1"),z2("z2"),z3("z3"),z4("z4");
symbol w1("w1"),w2("w2"),w3("w3"),w4("w4");
symbol n1("n1"),n2("n2"),n3("n3"),n4("n4");
ex zlist=lst{z1,z2,z3,z4};
ex wlist=lst{w1,w2,w3,w4};
ex nlist=lst{n1,n2,n3,n4};


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
    }
    void display(){
        if(this->coeff==0){
            cout << "0" << endl;
        }
        else{
            if(this->coeff!=1)cout << "(" << this->coeff << ")*";
            cout << "I[";
            for(int i=0;i<SDim;i++){
                if(i>0)cout<<",";
                cout << this->index[i] ;
            }
            cout << "]" << endl;
        }
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
//Index Polynomial
class IndPol{
public:
    vector<IndMon> terms={};
    void set_from_indmon(IndMon mon){
        this -> terms={mon};
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
                cout << "I[";
            }
            else{
                cout << "(" << c << ")*I[";
            }
            
            for(j=0;j<SDim;j++){
                if(j>0)cout <<",";
                cout << this->terms[i].index[j];
            }
            cout << "]";
        }
        cout << endl;
    }
    void collect(){
        int i,j,n=0;//n is the current term number of result
        int N = this->terms.size();
        while(true){
            if(n>=N-1)break;//here, N-1, because if only 1 term left, no need to continue
            i=n+1;// manual for loop
            while(true){
                if(i>=N)break;
                if(SameIndexQ(
                    this->terms[n].index,
                    this->terms[i].index,
                    SDim
                )){
                    this->terms[n].coeff+=
                        this->terms[i].coeff;
                    this->terms.erase(this->terms.begin()+i);
                    N--;
                }
                else{
                    i++;
                }
                //if(i==N)break;
            }
            n++;
        }
        //delete 0 terms
        n = this->terms.size();
        i=0;
        while(true){
            if(i>=n)break;
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
    
    void operator=(IndMon mon){
        (*this).set_from_indmon(mon);
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
IndPol ind_pol_collect(IndPol pol){
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
int main()
{   
    IndMon m1,m2,m3;
    m1=z1*z2*w4*w3*n2*n4;
    m2=pow(z1,4)*z2*z3;
    m3=z1*w1*w2*z3*w4*(n1+n2);
    cout << "m1=";m1.display();
    cout << "m2=";m2.display();
    cout << "m3=";m3.display();
    IndPol pol=m1+m2;
    cout << "m1+m2=";pol.display();
    cout <<"[m1+m2,m3]=";(pol*m3-m3*pol).display();
    cout <<"1/m3=";(1/m3).display();
    cout <<"(m1+m2)/m3=";(pol/m3).display();
    cout <<"(1/m3)*(m1+m2)=";((1/m3)*(m1+m2)).display();
    return 0;
}