#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}
int mminvprime(int a, int b) {return expo(a, b - 2, b);}
int mod_add(int a, int b, int m) {a = a % m; b = b % m; return (((a + b) % m) + m) % m;}
int mod_mul(int a, int b, int m) {a = a % m; b = b % m; return (((a * b) % m) + m) % m;}
int mod_sub(int a, int b, int m) {a = a % m; b = b % m; return (((a - b) % m) + m) % m;}
int mod_div(int a, int b, int m) {a = a % m; b = b % m; return (mod_mul(a, mminvprime(b, m), m) + m) % m;}  //only for prime m

vector<int> hashPrimes = {1000000009, 100000007};
vector<vector<int>> powersOfBase,inversePowersOfBase;

void findInversePower(int primes, int n){
    const int base = 31;
    powersOfBase.resize(primes);
    inversePowersOfBase.resize(primes);
    for(int i = 0; i < hashPrimes.size(); i++) {
        powersOfBase[i].resize(n + 1);
        inversePowersOfBase[i].resize(n + 1);
        powersOfBase[i][0] = 1;
        for(int j = 1; j <= n; j++){
            powersOfBase[i][j] = (base * powersOfBase[i][j - 1]) % hashPrimes[i];
        }
        inversePowersOfBase[i][n] = mminvprime(powersOfBase[i][n], hashPrimes[i]);
        for(int j = n - 1; j >= 0; j--){
            inversePowersOfBase[i][j] = mod_mul(inversePowersOfBase[i][j + 1], base, hashPrimes[i]);
        }
    }
}

struct Hashing{
    string s;
    int n;
    int primes;
    vector<vector<int>> hashValues;
    Hashing(string a){
        primes = hashPrimes.size();
        hashValues.resize(primes);
        s = a;
        n = s.length();
        if(inversePowersOfBase.empty()) findInversePower(primes,n);
        for(int i = 0; i < hashPrimes.size(); i++) {
            hashValues[i].resize(n);
            for(int j = 0; j < n; j++){
                hashValues[i][j] = ((s[j] - 'a' + 1ll) * powersOfBase[i][j]) % hashPrimes[i];
                hashValues[i][j] = (hashValues[i][j] + (j > 0ll ? hashValues[i][j - 1] : 0ll)) % hashPrimes[i];
            }
        }
    }
    vector<int> substringHash(int l, int r){
        vector<int> hash(primes);
        for(int i = 0; i < primes; i++){
            int val1 = hashValues[i][r];
            int val2 = l > 0ll ? hashValues[i][l - 1] : 0ll;
            hash[i] = mod_mul(mod_sub(val1, val2, hashPrimes[i]), inversePowersOfBase[i][l], hashPrimes[i]);
        }
        return hash;
    }
    bool compareSubstrings(int l1, int r1, int l2, int r2){
        if(l1 > l2){
            swap(l1, l2);
            swap(r1, r2);
        }
        for(int i = 0; i < primes; i++){
            int val1 = mod_sub(hashValues[i][r1], (l1 > 0 ? hashValues[i][l1 - 1] : 0LL), hashPrimes[i]);
            int val2 = mod_sub(hashValues[i][r2], (l2 > 0 ? hashValues[i][l2 - 1] : 0LL), hashPrimes[i]);
            if(mod_mul(val1, powersOfBase[i][l2 - l1], hashPrimes[i]) != val2)
                return false;
        }   
        return true;
    }

    bool check(int r){
        vector<int> hashes = substringHash(0,r);
        for(int i = 1; ++r<n-1; i++){
            vector<int>currHash = substringHash(i,r);
            if(hashes==currHash){
                return true;
            }
        }
        return false;
    }
};

void solve()
{
    string str;
    cin>>str;
    Hashing s(str);
    vector<int>len;
    for(int i = 0; i<sz(str)-1; i++){
        if(s.compareSubstrings(0,i,sz(str)-1-i,sz(str)-1))
            len.push_back(i);
    }
    int l = 0, r = sz(len)-1;
    while(l<=r){
        int mid = (l+r)/2;
        int curr = len[mid];
        if(s.check(curr)){
            l = mid+1;
        }else{
            r = mid-1;
        }
    }
    if(r>=0 and r<sz(len)){
        cout<<str.substr(0,len[r]+1)<<endl;
    }else{
        cout<<"Just a legend"<<endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}