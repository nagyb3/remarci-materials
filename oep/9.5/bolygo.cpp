#include "bolygo.h"
#include "csillaghajo.h"

bool Bolygo::maxTuzero(int &outMaxTuzero, Csillaghajo* &outHajo) const{
    if (hajok.size() == 0){
        return false;
    }
    outMaxTuzero = hajok[0]->tuzero();
    outHajo = hajok[0];
    for ( Csillaghajo* h : hajok ){
        if (outMaxTuzero < h->tuzero()){
            outMaxTuzero = h->tuzero();
            outHajo = h;
        }
    }
    return true;
}
int Bolygo::osszPajzs() const {
    int p = 0;
    for ( Csillaghajo* h : hajok ){
        p += h->pajzs;
    }
    return p;
}