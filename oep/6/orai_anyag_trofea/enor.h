#pragma once

#include <fstream>
#include <sstream>
#include <string>

struct Trofea{
	std::string nev;
	std::string datum;
	std::string fajta;
	unsigned int suly;
	friend std::ifstream& operator>>(std::ifstream& is, Trofea& t);
};

std::ifstream& operator>>(std::ifstream& is, Trofea& t){
	is >> t.nev >> t.datum >> t.fajta >> t.suly;
	return is;
}


class Enor{
	private:
		enum Status { norm, abnorm };
		Trofea dx;
		Status sx;
		bool akt;
		bool vege;
		std::ifstream x;
		void read();
	public:
		class FileErrorException : public std::exception { };
		Enor(const std::string &str);
		void first() { read(); next(); }
		void next();
		bool current() { return akt; }
		bool end() { return vege; }
};

Enor::Enor(const std::string &str)
{
	x.open(str);
	if(x.fail()){
		throw FileErrorException();
	}
}

void Enor::read(){
	sx = (x >> dx) ? norm : abnorm;
}

void Enor::next(){
	vege = (sx == abnorm);
	if (!vege){
		akt = false;
		std::string nev = dx.nev;
		while (sx == norm && dx.nev == nev){
			akt = akt || (dx.fajta == "medve");
			/*if (dx.fajta == "medve"){
				akt = true;
			}*/
			read();
		}
	}
}