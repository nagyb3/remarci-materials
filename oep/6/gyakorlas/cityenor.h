#pragma once

#include <fstream>
#include <sstream>
#include <string>

struct City {
	std::string countryName;
	std::string cityName;
	bool aboveThree;
	int sightNumber; //otos
};

inline std::ostream& operator<<(std::ostream& os, const City& e){
	os << e.countryName << " " << e.cityName << " " << (e.aboveThree?"Igen":"Nem") << " " << e.sightNumber;
	return os;
}


struct Sight{
	std::string sightName;
	int points;
};

class CityEnor{
	private:
		std::ifstream _f;
		City _cur;
		bool _end;
	public:
		class FileErrorException : public std::exception { };
		CityEnor(const std::string &str);
		void first() {next();}
		void next();
		City current() const { return _cur;}
		bool end() const { return _end;}
};

CityEnor::CityEnor(const std::string &str)
{
	_f.open(str);
	if(_f.fail()){
		throw FileErrorException();
	}
}

void CityEnor::next()
{
	std::string line;
	getline(_f , line);
	_end = _f.fail();
	if( !_end ){
		std::istringstream is(line);
		is >> _cur.countryName >> _cur.cityName;
		_cur.aboveThree = true;
		_cur.sightNumber = 0;
		std::string sightName;
		int sightPoints;
		while (is >> sightName >> sightPoints){
			if (sightPoints < 3){
				_cur.aboveThree = false;
			}
			++_cur.sightNumber;
		}
	}
}
