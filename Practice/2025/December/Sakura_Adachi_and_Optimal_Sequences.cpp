#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e6 + 3;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
const int N = mod;
int n,fact[N];

bool check(int add, int &c, int &t, int &mult){
	return ((c + add) << mult) <= t;
}

int bs(int l, int r, int &c, int &t, int &mult){
	if(l > r)
		return r;
	int mid = (l + r) >> 1;
	if(check(mid, c, t, mult))
		return bs(mid + 1, r, c , t, mult);
	return bs(l, mid - 1, c, t, mult);
}

int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}

int mminvprime(int a) {return expo(a, mod - 2, mod);}

int calc1(vector<int> &a, vector<int> &b, int mult, int &operation){
	debug(mult)
	vector<int> v;
	for(int i = 0; i < n; i++){
		int add = bs(0,mod,a[i],b[i],mult);
		debug(a[i]) debug(b[i]) debug(add)
		if(add){
			v.push_back(add);
			operation += add;
			a[i] += add;
		}
	}
	if(operation >= mod)
		return 0;
	int ans = fact[operation];
	for(auto &x: v){
		ans = (ans * mminvprime(fact[x])) % mod;
	}
	return ans % mod;
}

int go(int a, int b){
	int res = 0;
	while((a<<1) <= b){
		a<<=1;
		res++;
	}
	return res;
}

void solve()
{
    int left = 1, right = 1, operation = 0, right_add = 0;
    cin >> n;
    vector<int> a(n), b(n);
    for(auto &x: a)
    	cin >> x;
    for(auto &x: b)
    	cin >> x;
    int mult = inf;
    for(int i = 0; i < n; i++){
    	if(a[i] == b[i]){
    		mult = 0;
    		break;
    	}
    	mult = min(mult,go(a[i], b[i]));
    }
    if(mult != 0){
    	left = calc1(a,b,mult,operation);
    	operation += mult;
    	for(auto &x: a){
    		x<<=mult;
    	}
    }
    vector<int> v;
    for(int i = 0; i < n; i++){
    	int add = b[i] - a[i];
    	right_add += add;
    	operation += add;
    	if(add)
    		v.push_back(add);
    }
    debug(a) debug(b) debug(v)
   	debug(right_add)
    if(right_add >= mod){
    	right = 0;
    }else{
    	right = fact[right_add];
    	for(auto &x: v){
			right = (right * mminvprime(fact[x])) % mod;
		}
    }
    cout << operation << " " << (left * right) % mod << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    fact[0] = 1;
    for(int i = 1; i < N; i++){
    	fact[i] = (fact[i - 1] * i) % mod;
    }
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}