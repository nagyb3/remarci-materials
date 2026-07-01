#pragma once

#include "bolygo.h"

#include <string>

class Csillaghajo
{
public:

    Csillaghajo(std::string n, int pan, int paj, int u ) : nev(n), pancel(pan), pajzs(paj), urgardista(u) {}
    virtual ~Csillaghajo(){}

    void ved(Bolygo* b) { bolygo = b; b->hajok.push_back(this); }
    virtual int tuzero() const = 0;

    std::string nev;
    int pancel;
    int pajzs;
    int urgardista;
    Bolygo* bolygo;
};

class Faltoro : public Csillaghajo
{
public:
    Faltoro(std::string n, int pan, int paj, int u ) : Csillaghajo(n, pan, paj, u) {}
    int tuzero() const override { return pajzs/2; }
};

class Partraszallo : public Csillaghajo
{
public:
    Partraszallo(std::string n, int pan, int paj, int u ) : Csillaghajo(n, pan, paj, u) {}
    int tuzero() const override { return urgardista; }
};

class Lezerezo : public Csillaghajo
{
public:
    Lezerezo(std::string n, int pan, int paj, int u ) : Csillaghajo(n, pan, paj, u) {}
    int tuzero() const override { return pancel; }
};
