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
#define inf 1e3
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

vector<int> hashPrimes = {1000000009};
static constexpr int base = 31, maxLen = 100010;
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
        if(powersOfBase.empty())
            precomputePowers();
        primes = sz(hashPrimes);
        hashValues.resize(primes);
        s = a;
        n = s.length();
        for(int i = 0; i < sz(hashPrimes); i++) {
            hashValues[i].resize(n);
            for(int j = 0; j < n; j++){
                hashValues[i][j] = ((s[j] - 'A' + 1ll) * powersOfBase[i][j]) % hashPrimes[i];
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
    int max_suffix_Len(Hashing &other){
        int max_len = min(n,other.n);
        for(int i = n-max_len; i<n; i++){
            if(substringHash(i,n-1)==other.substringHash(0,n-i-1)){
                return n-i;
            }
        }
        return 0;
    }
    bool find_hash(vector<int>to_find, int len){
        for(int i = 0; i+len<=n; i++){
            if(substringHash(i,i+len-1)==to_find)
                return true;
        }
        return false;
    }
};

int final_mask,N;
vector<string>new_strings;
vector<Hashing>new_hashes;
vector<vector<int>>dp,add;

int f(int mask, int pos){
    if(mask==final_mask)
        return dp[mask][pos] = 0;
    int &ans = dp[mask][pos];
    if(ans!=inf)
        return ans;
    for(int i = 0; i<N; i++){
        if((mask&(1<<i))==0){
            int new_mask = mask|(1<<i);
            if(add[pos][i]==-1){
                add[pos][i] = sz(new_strings[i]) - new_hashes[pos].max_suffix_Len(new_hashes[i]);
            }
            ans = min(ans,f(new_mask,i) + add[pos][i]);
        }
    }
    return ans;
}

void solve()
{
    new_strings.clear();
    new_hashes.clear();
    dp.clear();
    add.clear();
    int n;
    cin>>n;
    vector<string>vs(n);
    readv(vs);
    vector<Hashing> hashes;
    for(int i = 0; i<n; i++){
        hashes.push_back(Hashing(vs[i]));
    }
    set<int>ers;
    for(int i = 0; i<sz(vs); i++){
        for(int j = 0; j<n; j++){
            if(j==i)
                continue;
            int len = sz(vs[j]);
            if(hashes[i].find_hash(hashes[j].substringHash(0,len-1), len)){
                ers.insert(j);
            }
        }
    }
    for(int  i = 0; i<n; i++){
        if(ers.count(i))
            continue;
        new_strings.push_back(vs[i]);
    }
    for(int  i = 0; i<n; i++){
        if(ers.count(i))
            continue;
        new_hashes.push_back(hashes[i]);
    }
    N = sz(new_strings);
    final_mask=(1<<N) - 1;
    dp.assign((1<<N),vector<int>(N,inf));
    add.assign(N,vector<int>(N,-1));
    int ans = inf, start = 0;
    for(int i = 0; i<N; i++){
        if(f(1<<i, i) < ans){
            ans = f(1<<i, i);
            start = i;
        }else if(f(1<<i, i) == ans){
            if(new_strings[i]<new_strings[start]){
                ans = f(1<<i, i);
                start = i;
            }
        }
    }
    string ans_str = new_strings[start];
    int mask = 1<<start,cnt = 0;
    while(mask!=final_mask){
        for(int i = 0; i<N; i++){
            if((mask&(1<<i))!=0)
                continue;
            if(ans==dp[(mask|(1<<i))][i]+add[start][i]){
                int ers = sz(new_strings[i]) - add[start][i];
                while(ers--)
                    ans_str.pop_back();
                ans_str+=new_strings[i];
                mask|=(1<<i);
                ans = dp[(mask|(1<<i))][i];
                start = i;
                break;
            }
        }
    }
    cout<<ans_str<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}