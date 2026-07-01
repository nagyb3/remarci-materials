#pragma once

#include "vad.h"


class Trofea {
    public:
        std::string helyszin;
        std::string datum;
        Vad* zsakmany;
        
        Trofea(const std::string& h, const std::string& d, Vad* zs) : helyszin(h), datum(d), zsakmany(zs) {}
        Trofea() {}

        friend std::istream& operator>>(std::istream& is, Trofea& t);
};

std::istream& operator>>(std::istream& is, Trofea& t){
    if (t.zsakmany != nullptr){
        delete t.zsakmany;
        t.zsakmany = nullptr;
    }
    is >> t.helyszin >> t.datum;
    std::string faj;
    is >> faj;

    double tom;
    std::string nem;
    is >> tom >> nem;
    if (faj == "oroszlan"){
        t.zsakmany = new Oroszlan(tom, nem=="him");
    } else if (faj == "orrszarvu"){
        double szt;
        is >> szt;
        t.zsakmany = new Orrszarvu(tom, nem=="him", szt);
    } else if (faj == "elefant") {
        double ja, ba;
        is >> ja >> ba;
        t.zsakmany = new Elefant(tom, nem=="him", ja, ba);
    }
    return is;
}