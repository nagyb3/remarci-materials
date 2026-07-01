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
	
	int hanyHimOroszlan() const;
	bool maxSzarvTomeg(double& max) const;
	bool egyezoAgyarhossz() const;
	void elejt(Vad* mit, const std::string& hol, const std::string& mikor);
	
	Vadasz(const std::string &n, int a, const std::string &fnev);
	~Vadasz();
};

Vadasz::Vadasz(const std::string &n, int k, const std::string &fnev) : nev(n), kor(k) {
	std::ifstream f(fnev);
	if(f.fail()){
		std::cerr << "File error" << std::endl; exit(1);
	}
	
	std::string sor, helyszin, datum, faj, nem;
    double tomeg, balagyar, jobbagyar, szarv;
    Vad* zsakmany;
    
	while(getline(f,sor)){
		std::istringstream is(sor);
		is >> helyszin >> datum >> faj >> tomeg >> nem;
		
		if(faj=="oroszlan"){
			zsakmany = new Oroszlan(tomeg, nem=="him");
		}else if(faj=="orrszarvu"){
			is >> szarv;
			zsakmany = new Orrszarvu(tomeg, nem=="him", szarv);
		}else if(faj=="elefant"){
			is >> balagyar >> jobbagyar;
			zsakmany = new Elefant(tomeg, nem=="him", balagyar, jobbagyar);
		}
		trofeak.push_back(new Trofea(helyszin, datum, zsakmany));
	}
}

Vadasz::~Vadasz(){
	for (int i = 0; i < trofeak.size(); ++i){
		delete trofeak[i];
	}
}

void Vadasz::elejt(Vad* mit, const std::string& hol, const std::string& mikor){
	trofeak.push_back(new Trofea(hol, mikor, mit));
}


int Vadasz::hanyHimOroszlan() const {
	int db = 0;
	for( Trofea* t : trofeak ){
		if( t->zsakmany->isOroszlan() && t->zsakmany->him ){
			++db;
		}
	}
	return db;
}

bool Vadasz::maxSzarvTomeg(double& max) const {
    bool l = false;
    for( Trofea* t : trofeak ){
		if(!t->zsakmany->isOrrszarvu()){
			//SKIP
		} else if (t->zsakmany->isOrrszarvu()) {
			Orrszarvu* o = (Orrszarvu*)t->zsakmany;
			double r = o->szarv / o->tomeg;
			if(!l) {
				l = true;
				max = r;
			} else if (max < r){
				max = r;
			}
		}
        
    }
    return l;
}
bool Vadasz::egyezoAgyarhossz() const {
    bool l = false;
    for( Trofea* t : trofeak ){
        Elefant* e = (Elefant*)t->zsakmany;
        if(l = e->bal == e->jobb){
			break;
		}
    }
    return l;
}