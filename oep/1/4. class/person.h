#pragma once

#include <iostream>
#include <fstream>

using namespace std;

class Person {
private:
    string name;
    int age;
    string location;
public:
    Person() {}
    /*void*/ Person(const string& n, const int& a, const string& l) : name(n), age(a), location(l) {
    	//Vagy pedig:
    	/*
    	name = n;
    	age = a;
    	location = l;
    	*/
    }

    string getName() const {return name;}
    int getAge() const {return age;}
    string getLocation() const {return location;}
    
    void setName(const string& n) {name = n;}
    //void setAge(const int& a) {age = a;}
    void setLocation(const string& l) {location = l;}
	
	void birthday(){
		++age;
	}
	
	void moveToJanosHegy(){
		location = "Janos hegy";
	}
	
	friend istream& operator>>(istream& is, Person& p)
	{
		is >> p.name >> p.age >> p.location;
		return is;
	}
	
	friend ostream& operator<<(ostream& os, const Person& p)
	{
		os << "Nev: " << p.name << ", kor:" << p.age << ", hely: " << p.location;
		return os;
	}
};

