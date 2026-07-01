#pragma once
#include "termek.h"
#include <vector>
#include <fstream>

class Reszleg
{
	public:
		Reszleg(const std::string &fnev);
		void kivesz(Termek* termek);

		std::vector<Termek*> keszlet;
};

Reszleg::Reszleg(const std::string &fnev)
{
	std::ifstream f(fnev);
	int i;
	std::string s;
	while (f >> s >> i) {
		keszlet.push_back(new Termek(s,i));
	}
	f.close();
}

void Reszleg::kivesz(Termek* termek)
{
	bool l = false;
	int ind;
	for( unsigned int i = 0; !l && i < keszlet.size(); ++i) {
		l = keszlet[i] == termek;
		ind = i;
	}
	if (l)  keszlet.erase(keszlet.begin()+ind);
}