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

vector<int> hashPrimes = {1000000009, 998244353};
static constexpr int base = 31, maxLen = 200010;
vector<vector<int>> powersOfBase, inversePowersOfBase;

void precomputePowers() {
    int primes = sz(hashPrimes);
    powersOfBase.resize(primes, vector<int>(maxLen + 1));
    inversePowersOfBase.resize(primes, vector<int>(maxLen + 1));
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

struct S{
    int value;

    S(int val = 0) : value(val) {}
};

S combine(S &a, S &b, int &m){
    return S((a.value+b.value)%m);
}

struct Segment_Tree{
    int n,m;
    vector<S>t;

    Segment_Tree(int _n,int _m,vector<int>&v){
        n = _n;
        m = _m;
        t.resize(2*n);
        for(int i = n; i<2*n; i++)
            t[i] = S(v[i-n]);
        build();
    }

    Segment_Tree(){
        n = 0;
        t.clear();
    }

    void build(){
        for (int i = n - 1; i > 0; --i) t[i] = combine(t[i<<1], t[i<<1|1],m);
    }

    void modify(int p, S value) {
        for (t[p += n] = value; p >>= 1; ) t[p] = combine(t[p<<1], t[p<<1|1],m);
    }

    S query(int l, int r) {
        S resl, resr;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l&1) resl = combine(resl, t[l++],m);
            if (r&1) resr = combine(t[--r], resr,m);
        }
        return combine(resl, resr,m);
    }
};

struct Hashing{
    string s;
    int n;
    int primes;
    vector<vector<int>> hashValues;
    vector<Segment_Tree>st; 
    Hashing(string a){
        primes = sz(hashPrimes);
        st.resize(primes);
        hashValues.resize(primes);
        if(powersOfBase.empty())
            precomputePowers();
        s = a;
        n = s.length();
        for(int i = 0; i < sz(hashPrimes); i++) {
            hashValues[i].resize(n);
            for(int j = 0; j < n; j++){
                hashValues[i][j] = ((s[j] - 'a' + 1ll) * powersOfBase[i][j]) % hashPrimes[i];
            }
            st[i] = Segment_Tree(n,hashPrimes[i],hashValues[i]);
        }
    }
    vector<int> substringHash(int l, int r){
        vector<int> hash(primes);
        for(int i = 0; i < primes; i++){
            int val = (st[i].query(l,r+1).value)%hashPrimes[i];
            val = (val*inversePowersOfBase[i][l])%hashPrimes[i];
            hash[i] = val;
        }
        return hash;
    }
    void update(int pos, char c){
        if(c==s[pos])
            return;
        s[pos] = c;
        for(int i = 0; i < primes; i++){
            hashValues[i][pos] = ((c - 'a' + 1ll) * powersOfBase[i][pos]) % hashPrimes[i];
            st[i].modify(pos,S(hashValues[i][pos]));
        }
    }
};

bool palindrome(Hashing& original, Hashing& reversed, int l1, int r1, int n){
    int l2 = n - r1 - 1, r2 = n - l1 - 1;
    debug(original.substringHash(l1, r1)) debug(reversed.substringHash(l2, r2))
    if(original.substringHash(l1, r1) == reversed.substringHash(l2, r2)){
        return true;
    }
    return false;
}

void solve()
{
    string str;
    int n,m;
    cin>>n>>m>>str;
    Hashing original(str);
    reverse(all(str));
    Hashing reversed(str);
    while(m--){
        int t;
        cin>>t;
        if(t==1){
            int pos;
            char c;
            cin>>pos>>c;
            pos--;
            int rpos = n-1-pos;
            original.update(pos,c);
            reversed.update(rpos,c);
        }else{
            int a,b;
            cin>>a>>b;
            a--;b--;
            if(palindrome(original,reversed,a,b,n))
                yes;
            else 
                no;
        }
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
    // cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}