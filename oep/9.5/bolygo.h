#pragma once

#include <vector>
#include <string>

class Csillaghajo;

class Bolygo
{
public:
    Bolygo(std::string n) : nev(n) {}
    bool maxTuzero(int &outMaxTuzero, Csillaghajo* &outHajo) const;
    int osszPajzs() const;

    std::string nev;
    std::vector<Csillaghajo*> hajok;
};