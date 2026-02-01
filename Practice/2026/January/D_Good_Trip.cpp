#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e9 + 7;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

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

const int N = 2e5 + 10;
int n, m, k, fact[N], ifact[N];

int nCk(int nn, int kk){
    return ((fact[nn] * ifact[kk]) % mod * ifact[nn - kk]) % mod;
}

void solve()
{
    cin >> n >> m >> k;
    int sum = 0, tmp, d = nCk(n, 2);
    for(int i = 0; i < m; i++){
        cin >> tmp >> tmp >> tmp;
        sum = (sum + tmp) % mod;
    }
    int fixed = ((k * sum) % mod * mminvprime(d)) % mod, contribution = 0;
    for(int i = 2; i <= k; i++){
        int choose = nCk(k, i);
        int chosen_p = expo(mminvprime(d), i);
        int not_chosen_p = expo(((d - 1 + mod) % mod * mminvprime(d)) % mod, k - i);
        int p = ((choose * chosen_p) % mod * not_chosen_p) % mod;
        int ap = ((i * (i - 1)) / 2) % mod;
        contribution = (contribution + (ap * p) % mod) % mod;
    }
    contribution = (contribution * m) % mod;
    cout << (fixed + contribution) % mod << endl;
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
    ifact[N - 1] = mminvprime(fact[N - 1]);
    for(int i = N - 2; i >= 0; i--){
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
    }

    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}