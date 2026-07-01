#pragma once

#include <iostream>
#include <vector>
#include <fstream>

struct FileContent{
	std::string vadaszNev;
	std::string fajta;
	int suly;
};

inline std::istream& operator>>(std::istream& is, FileContent& e) {
    is >> e.vadaszNev >> e.fajta >> e.suly;
    return is;
}

struct Vadasz{
	std::string vadaszNev;
	bool vanMedve;
};

inline std::ostream& operator<<(std::ostream& os, const Vadasz& e){
	os << e.vadaszNev << " " << (e.vanMedve?"Igen":"Nem");
	return os;
}

class VadaszEnor{
public:
	class FileErrorException : public std::exception { };
	enum Status { norm, abnorm };
	
	VadaszEnor(const std::string& fileName);
	
	void first();
	void next();
	bool end() const { return isEnd; }
	Vadasz current() const { return dx; }
private:
	FileContent currentRead;
	
	bool isEnd;
	
	void read();
	
	Status sx;
	Vadasz dx;
	std::fstream f;
};




VadaszEnor::VadaszEnor(const std::string& fileName){
	f.open(fileName.c_str());
	if (f.fail()){
		throw FileErrorException;
	}
}

void VadaszEnor::next(){
	isEnd = (sx == abnorm);
	dx.vadaszNev = currentRead.vadaszNev;
	bool medve = false;
	while (dx.vadaszNev == currentRead.vadaszNev && sx == norm){
		if (currentRead.fajta == "medve"){
			medve = true;
		}
		read();
	}
	dx.vanMedve = medve;
}

void VadaszEnor::first(){
	read();
	next();
}

void VadaszEnor::read(){
	if (f >> currentRead){
		sx = norm;
	} else {
		sx = abnorm;
	}
}
