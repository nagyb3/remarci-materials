#pragma once
#include "uzlet.h"
#include <string>
#include <vector>

class Vasarlo
{
	public:
		Vasarlo(const std::string &fnev);
		void vasarol(const Uzlet &s);
		bool keres(std::string nev, Reszleg* reszleg, Termek *&termek) const;
		bool olcsotKeres(std::string nev, Reszleg* reszleg, Termek *&termek) const;
		std::vector<Termek*> kosar;

	private:
		std::string nev;
		std::vector<std::string> bevasarlo_lista;

		void vesz(Termek* t, Reszleg* r);
};

Vasarlo::Vasarlo(const std::string &fnev)
{
	std::ifstream f;
	f.open(fnev.c_str());

	f >> nev;
	std::string s;
	while(f >> s) {
		bevasarlo_lista.push_back(s);
	}
	f.close();
}

void Vasarlo::vesz(Termek* t, Reszleg* r)
{
	kosar.push_back(t);
	r->kivesz(t);
	std::cout << t->getNev() << " " << t->getAr() << std::endl;
}

void Vasarlo::vasarol(const Uzlet &u)
{
	std::cout << nev << " vasarlo megvette az alabbi arukat: \n";
	for (std::string termekNev : bevasarlo_lista) {
		Termek *termek;
		bool l = keres(termekNev, u.elelmiszer, termek);
		if (l) {
			vesz(termek, u.elelmiszer);
		}
	}
	for (std::string termekNev : bevasarlo_lista) {
		Termek *termek;
		bool l = olcsotKeres(termekNev, u.muszaki, termek);
		if (l) {
			vesz(termek, u.muszaki);
		}
	}
}

bool Vasarlo::keres(std::string nev, Reszleg* reszleg, Termek* &termek) const
{
	bool l = false;
	for(Termek* t : reszleg->keszlet ) {
		if ( ( l = (nev == t->getNev()) ) ) {
		    termek = t; break;
		}
	}
	return l;
}

bool Vasarlo::olcsotKeres(std::string nev, Reszleg* reszleg, Termek* &termek) const
{
	bool l = false;
	int min;
	for(Termek* t : reszleg->keszlet )  {
		if (t->getNev() != nev) continue;
		if (l) {
		    if (min > t->getAr()) {
		        min = t->getAr();
		        termek = t;
		    }
		}
		else  {
		    l=true;
		    min = t->getAr();
		    termek = t;
		}
	}
	return l;
}