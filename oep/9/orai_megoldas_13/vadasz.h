#pragma once

#include <vector>
#include <sstream>
#include <fstream>
#include "trofea.h"

class Vadasz {
    public:
        std::string nev;
        int kor;
        std::vector<Trofea*> trofeak;

        Vadasz(const std::string& n, int k, const std::string& fnev);
        ~Vadasz();

        int hanyHimOroszlan() const;
        double maxSzarvTomeg() const;
        bool egyezoAgyarhossz() const;

        void elejt(Vad* mit, const std::string& hol, const std::string& mikor);
};

int Vadasz::hanyHimOroszlan() const{
    int db = 0;
    for (Trofea* e : trofeak){
        if (e->zsakmany->isOroszlan() && e->zsakmany->him){
            ++db;
        }
    }
    return db;
}
double Vadasz::maxSzarvTomeg() const{
    return 0;
}
bool Vadasz::egyezoAgyarhossz() const{
    return false;
}

void Vadasz::elejt(Vad* mit, const std::string& hol, const std::string& mikor){
    trofeak.push_back(new Trofea(hol, mikor, mit));
}

Vadasz::Vadasz(const std::string& n, int k, const std::string& fnev) : nev(n), kor(k) {
    std::ifstream f(fnev);
    if (f.fail()){
        std::cerr << "File hiba" << std::endl; exit(1);
    }   

    std::string sor;
    Trofea* trofea_tmp;
    while (getline(f, sor)){
        trofea_tmp = new Trofea();
        std::istringstream ss(sor);
        ss >> *trofea_tmp;
        trofeak.push_back(trofea_tmp);
    }
}

Vadasz::~Vadasz(){
    for (int i = 0; i < trofeak.size(); ++i){
        delete trofeak[i];
    }
}