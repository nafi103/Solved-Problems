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

const int N = 2e6 + 10;
int fact[N], ifact[N];

int expo(int a, int b){
    int res = 1;
    while(b){
        if(b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}

int inv(int a){
    return expo(a, mod - 2);
}

int nCr(int n, int r){
    if(n < r)
        return 0;
    return ((fact[n] * ifact[r]) % mod * ifact[n - r]) % mod;
}

void solve()
{
    int k;
    string str;
    cin >> k >> str;
    int n = sz(str);

    int ans = 0;
    for(int i = 0; i <= k; i++){
        int possible_back = expo(26, i);

        int stars = k - i, bars = n - 1;
        int possible_front = (expo(25, stars) * nCr(stars + bars, bars)) % mod;

        ans = (ans + (possible_back * possible_front) % mod) % mod;
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

    fact[0] = 1;
    for(int i = 1; i < N; i++){
        fact[i] = (fact[i - 1] * i) % mod;
    }
    ifact[N - 1] = inv(fact[N - 1]);
    for(int i = N - 2; i >= 0; i--){
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
    }

    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}