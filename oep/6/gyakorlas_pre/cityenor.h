#pragma once

#include <fstream>
#include <sstream>
#include <string>

struct City {
	std::string countryName;
	std::string cityName;
	bool aboveThree;
	//int sightNumber; //otos
};

inline std::ostream& operator<<(std::ostream& os, const City& e){
	os << e.countryName << " " << e.cityName << " " << (e.aboveThree?"Igen":"Nem"); // << " " << e.sightNumber;
	return os;
}


struct Sight{
	std::string sightName;
	int points;
};

class CityEnor{
	private:
		//TODO
	public:
		class FileErrorException : public std::exception { };
		CityEnor(const std::string &str);
		//TODO
};

CityEnor::CityEnor(const std::string &str)
{
	_f.open(str);
	if(_f.fail()){
		throw FileErrorException();
	}
}