//Készítette:    Veszprémi Anna
//Dátum:         2019.02.19.
//Prioritásos sor header állománya

#pragma once

#include <iostream>
#include <vector>
#include "read.hpp"

//A prioritásos sor elemei egy egészből (prioritás) és egy szövegből állnak
//Az elem típusát megvalósító struct

//segéd függvény az ellenőrzött beolvasáshoz.
//Többszörös deklaráció elkerülése miatt inline
inline bool valid(int a){return true;}

struct Item
{
    //publikus adattagok
    int pr;
    std::string data;

    //Paraméter nélküli (üres)-, és paraméteres konstruktor
    Item() {};
    Item(int p,std::string s):pr(p), data(s) {}
};

//A prioritásos sor felülete
class PrQueue
{
    public:
        class PrQueueEmpty : public std::exception{};

        void add(const Item &a);
        Item remMax();          //legnagyobb prioritássú elem kivétele a sorból
        Item getMax() const;    //(egyik) legnagyobb prioritású elem visszaadása
        bool isEmpty()const;    //pr.sor ürességét vizsgálja

    private:
        std::vector<Item> _seq;
};
