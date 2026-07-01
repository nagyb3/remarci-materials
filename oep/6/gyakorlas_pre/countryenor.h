#pragma once

#include "cityenor.h"
#include <string>

struct Country {
	std::string countryName;
	bool hasSightlessCity;
};

inline std::ostream& operator<<(std::ostream& os, const Country& e){
	os << e.countryName << " " << (e.hasSightlessCity?"Igen":"Nem");
	return os;
}

class CountryEnor{
	private:
		//TODO
	public:
		CountryEnor(const std::string &str): _tt(str) { };
		void first() {_tt.first(); next();}
		void next();
		Country current() const { return _cur;}
		bool end() const { return _end;}
};

void CountryEnor::next()
{
	//TODO
}