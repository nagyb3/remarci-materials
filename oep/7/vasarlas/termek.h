#pragma once
#include <string>

class Termek
{
	private:
		std::string nev;
		int ar;
	public:
		Termek(std::string n, int a) : nev(n), ar(a) {}
		std::string getNev() {return nev;}
		int getAr() {return ar;}
};
