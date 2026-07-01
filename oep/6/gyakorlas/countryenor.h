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
		CityEnor _tt;
		Country _cur;
		bool _end;
	public:
		CountryEnor(const std::string &str): _tt(str) { };
		void first() {_tt.first(); next();}
		void next();
		Country current() const { return _cur;}
		bool end() const { return _end;}
};

void CountryEnor::next()
{
	_end = _tt.end();
	if(!_end){
		_cur.countryName = _tt.current().countryName;
		_cur.hasSightlessCity = false;
		while (!_tt.end() && _tt.current().countryName == _cur.countryName){
			if (_tt.current().sightNumber == 0){
				_cur.hasSightlessCity = true;
			}
			_tt.next();
		}
	}
}
