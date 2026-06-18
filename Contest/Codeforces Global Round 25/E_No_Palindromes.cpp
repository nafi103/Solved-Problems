#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}
int mminvprime(int a, int b) {return expo(a, b - 2, b);}
 vector<int> hashPrimes = {1000000009, 1000000007};
static constexpr int base = 31, maxLen = 1000010;
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
    vector<int> substringHash(int l, int r){
        vector<int> hash(primes);
        for(int i = 0; i < primes; i++){
            int val1 = hashValues[i][r];
            int val2 = l > 0 ? hashValues[i][l - 1] : 0ll;
            hash[i] = ((((val1- val2)%hashPrimes[i] + hashPrimes[i])%hashPrimes[i]) * inversePowersOfBase[i][l]) % hashPrimes[i];
        }
        return hash;
    }
};
 bool is_palindrome(Hashing& original, Hashing& reversed, int &n, int l, int r){
    int lp = n - r - 1, rp = n - l - 1;
    if(original.substringHash(l, r) == reversed.substringHash(lp, rp)){
        return true;
    }
    return false;
}
 void solve()
{
    string str;
    cin >> str;
    int n = sz(str);
    string rstr = str;
    reverse(all(rstr));
    if(str != rstr){
        cout << "YES" << endl;
        cout << 1 << endl;
        cout << str << endl;
        return;
    }
    Hashing original(str), reversed(rstr);
    for(int i = 1; i < n - 2; i++){
        if(is_palindrome(original, reversed, n, 0, i) == false and
            is_palindrome(original, reversed, n, i + 1, n - 1) == false){
            cout << "YES" << endl;
            cout << 2 << endl;
            for(int j = 0; j <= i; j++)
                cout << str[j];
            cout << " ";
            for(int j = i + 1; j < n; j++)
                cout << str[j];
            cout << endl;
            return;
        }
    }
    cout << "NO" << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}