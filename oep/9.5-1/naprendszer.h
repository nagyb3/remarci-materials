#pragma once

#include <array>

#include "naprendszer.h"
#include "bolygo.h"


class Naprendszer
{
private:
    Naprendszer(){}
    static Naprendszer* _instance;
public:
    static Naprendszer* Instance() { if(nullptr == _instance) _instance = new Naprendszer(); return _instance; }
    ~Naprendszer(){ if(nullptr!=_instance) delete _instance; }
    bool maxTuzero(Csillaghajo* &ship) const;
    Bolygo* vedtelen() const;

    std::array<Bolygo*,3> bolygok;
};

Naprendszer* Naprendszer::_instance = nullptr;

bool Naprendszer::maxTuzero(Csillaghajo* &maxHajo) const
{
    if (bolygok.size() == 0){
        return false;
    }
    bool l = false;
    int maxOm;
    for (Bolygo* b : bolygok){
        int om;
        Csillaghajo* csh;
        bool bmt = b->maxTuzero(om,csh);
        if (!l && bmt){
            l = true;
            maxHajo = csh;
            maxOm = om;
        } else if (l && bmt){
            if (maxOm < om){
                maxHajo = csh;
            }
        }
    }
    return l;
}

Bolygo* Naprendszer::vedtelen() const
{
    for (Bolygo* b : bolygok){
        if (b->hajok.size() == 0){
            return b;
        }
    }
    return nullptr;
}