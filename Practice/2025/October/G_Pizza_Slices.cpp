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
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
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

vector<int> hashPrimes = {1000000009, 1000000007};
static constexpr int base = 31, maxLen = 200010;
vector<vector<int>> powersOfBase, inversePowersOfBase;

void precomputePowers() {
    int primes = hashPrimes.size();
    powersOfBase.assign(primes, vector<int>(maxLen + 1));
    inversePowersOfBase.assign(primes, vector<int>(maxLen + 1));
    for (int i = 0; i < primes; i++) {
        powersOfBase[i][0] = 1;
        for (int j = 1; j <= maxLen; j++) {
            powersOfBase[i][j] = (base * powersOfBase[i][j - 1]) % hashPrimes[i];
        }
        inversePowersOfBase[i][maxLen] = mminvprime(powersOfBase[i][maxLen], hashPrimes[i]);
        for (int j = maxLen - 1; j >= 0; j--) {
            inversePowersOfBase[i][j] = (inversePowersOfBase[i][j + 1]* base)% hashPrimes[i];
        }
    }
}

struct Hashing{
    string s;
    int n;
    int primes;
    vector<vector<int>> hashValues;
    Hashing(string a){
        primes = sz(hashPrimes);
        hashValues.resize(primes);
        if(powersOfBase.empty())
            precomputePowers();
        s = a;
        n = s.length();
        for(int i = 0; i < sz(hashPrimes); i++) {
            hashValues[i].resize(n);
            for(int j = 0; j < n; j++){
                hashValues[i][j] = ((s[j] - 'a' + 1ll) * powersOfBase[i][j]) % hashPrimes[i];
                hashValues[i][j] = (hashValues[i][j] + (j > 0 ? hashValues[i][j - 1] : 0ll)) % hashPrimes[i];
            }
        }
    }
    pair<int,int> substringHash(int l, int r){
        pair<int,int> hash;
        for(int i = 0; i < primes; i++){
            int val1 = hashValues[i][r];
            int val2 = l > 0 ? hashValues[i][l - 1] : 0ll;
            if(i==0)
                hash.first = ((((val1- val2)%hashPrimes[i] + hashPrimes[i])%hashPrimes[i]) * inversePowersOfBase[i][l]) % hashPrimes[i];
            else
                hash.second = ((((val1- val2)%hashPrimes[i] + hashPrimes[i])%hashPrimes[i]) * inversePowersOfBase[i][l]) % hashPrimes[i];
        }
        return hash;
    }
};

void solve()
{
    int n,k;
    cin>>n>>k;
    set<pair<int,int>>s;
    string str;
    cin>>str;
    str+=str;
    Hashing h(str);
    reverse(all(str));
    Hashing h2(str);
    for(int i = k-1; i<2*n; i++){
        s.insert(h.substringHash(i-k+1,i));
    }
    for(int i = k-1; i<2*n; i++){
        s.insert(h2.substringHash(i-k+1,i));
    }
    cout<<sz(s)<<endl;
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}