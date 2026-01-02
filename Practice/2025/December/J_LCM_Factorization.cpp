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

const int N = 3e5 + 10;
int n, k, a[N], fact[N], ifact[N];
vector<int> spf(N);

int expo(int a, int b){
    int res = 1;
    while(b > 0){
        if(b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}

int mminvprime(int a){
    return expo(a, mod - 2);
}

int nCk(int n, int k){
    return ((fact[n] * ifact[k]) % mod * ifact[n - k]) % mod;
}

void add_distinct_primes(map<int,int> &mp, int x){
    while(x > 1){
        int p = spf[x];
        mp[p]++;
        while(x % p == 0)
            x/=p;
    }
}

void input(){
    cin >> n >> k;
    for(int i = 0; i < n; i++)
        cin >> a[i];
}

void solve()
{
    input();
    map<int,int> mp;
    for(int i = 0; i < n; i++){
        add_distinct_primes(mp, a[i]);
    }
    int ans = 0;
    for(auto [p,s]: mp){
        int present = 0;
        // Inclusion-Exclusion Principle to find how many time p is present in all subset array
        for(int i = 1; i <= min(s , k); i++){
            int choose_p = nCk(s, i); // Choosing i numbers which has p in it
            int rem_places = nCk(n - i, k - i); // Filling remaining k - i places
            if(i & 1){
                present = (present + (choose_p * rem_places) % mod) % mod;
            }else{
                present = (present - (choose_p * rem_places) % mod + mod) % mod;
            }
        }
        ans = (ans + (present * p)) % mod;
    }
    cout << ans << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);

    //Precalculate factorials and inverse factorials
    fact[0] = 1;
    for(int i = 1; i < N; i++){
        fact[i] = (fact[i - 1] * i) % mod;
    }
    ifact[N - 1] = mminvprime(fact[N - 1]);
    for(int i = N - 2; i >= 0; i--){
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
    }

    //Smallest Prime Factor
    iota(all(spf), 0);
    for(int i = 2; i * i < N; i++){
        if(spf[i] == i){
            for(int j = i + i; j < N; j+=i){
                spf[j] = min(spf[j], i);
            }
        }
    }
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}