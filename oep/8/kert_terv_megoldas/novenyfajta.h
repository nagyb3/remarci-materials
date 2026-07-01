#pragma once

class Novenyfajta{
	protected:
		int eresido;
		Novenyfajta(int e): eresido(e) {}
	public:
		virtual bool isHaszon() { return false; }
		virtual bool isVirag() { return false; }
		int getEresido() { return eresido; }
};

class Haszon : public Novenyfajta {
	protected: Haszon(int e) : Novenyfajta(e) {}
	public: bool isHaszon() override { return true; }
};

class Virag : public Novenyfajta {
	protected: Virag(int e) : Novenyfajta(e) {}
	public: bool isVirag() override { return true; }
};

class Burgonya : public Haszon
{
    public:
		static Burgonya* instance(){
			if (_instance == nullptr){ _instance = new Burgonya(); }
			return _instance;
		}
		static void destroy(){
			if (_instance != nullptr) { delete _instance; }
			_instance = nullptr;
		}
    private:
		static Burgonya* _instance;
        Burgonya() : Haszon(5) {}
};
Burgonya* Burgonya::_instance;

class Borso : public Haszon
{
    public:
		static Borso* instance(){
			if (_instance == nullptr){ _instance = new Borso(); }
			return _instance;
		}
		static void destroy(){
			if (_instance != nullptr) { delete _instance; }
			_instance = nullptr;
		}
    private:
		static Borso* _instance;
        Borso() : Haszon(6) {}
};
Borso* Borso::_instance;

class Hagyma : public Haszon
{
    public:
		static Hagyma* instance(){
			if (_instance == nullptr){ _instance = new Hagyma(); }
			return _instance;
		}
		static void destroy(){
			if (_instance != nullptr) { delete _instance; }
			_instance = nullptr;
		}
    private:
		static Hagyma* _instance;
        Hagyma() : Haszon(7) {}
};
Hagyma* Hagyma::_instance;


class Tulipan : public Virag
{
    public:
		static Tulipan* instance(){
			if (_instance == nullptr){ _instance = new Tulipan(); }
			return _instance;
		}
		static void destroy(){
			if (_instance != nullptr) { delete _instance; }
			_instance = nullptr;
		}
    private:
		static Tulipan* _instance;
        Tulipan() : Virag(1) {}
};
Tulipan* Tulipan::_instance;

class Szegfu : public Virag
{
    public:
		static Szegfu* instance(){
			if (_instance == nullptr){ _instance = new Szegfu(); }
			return _instance;
		}
		static void destroy(){
			if (_instance != nullptr) { delete _instance; }
			_instance = nullptr;
		}
    private:
		static Szegfu* _instance;
        Szegfu() : Virag(2) {}
};
Szegfu* Szegfu::_instance;

class Rozsa : public Virag
{
    public:
		static Rozsa* instance(){
			if (_instance == nullptr){ _instance = new Rozsa(); }
			return _instance;
		}
		static void destroy(){
			if (_instance != nullptr) { delete _instance; }
			_instance = nullptr;
		}
    private:
		static Rozsa* _instance;
        Rozsa() : Virag(3) {}
};
Rozsa* Rozsa::_instance;