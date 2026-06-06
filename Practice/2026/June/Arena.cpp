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

const int N = 2e5 + 10;
int fact[N], ifact[N];

int expo(int base, int exp){
    int res = 1;
    while(exp){
        if(exp & 1)
            res = (res * base) % mod;
        base = (base * base) % mod;
        exp >>= 1;
    }
    return res;
}

int inv(int a){
    return expo(a, mod - 2);
}

void precalculate(){
    fact[0] = 1;
    for(int i = 1; i < N; i++){
        fact[i] = (fact[i - 1] * i) % mod;
    }

    ifact[N - 1] = inv(fact[N - 1]);
    for(int i = N - 2; i >= 0; i--){
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
    }
}

int nCr(int n, int r) {
    if (r < 0 or r > n) return 0;
    return fact[n] * ifact[r] % mod * ifact[n - r] % mod;
}

vector<vector<int>> dp;

int f(int i, int j){
    if(i == 0)
        return 1;
    if(j <= 0 or i == 1)
        return 0;
    int &ans = dp[i][j];
    if(ans != -1)
        return ans;

    ans = (expo(min(i - 1, j), i) * f(0, j - i + 1)) % mod; 

    for(int k = 2; k <= i; k++){
        ans = (ans + (nCr(i, k) * expo(min(i - 1, j), i - k)) % mod * f(k, j - i + 1)) % mod;
    }

    return ans;
}

void solve()
{
    int n, x;
    cin >> n >> x;
    dp.assign(n + 1, vector<int> (x + 1, -1));
    cout << f(n, x) << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);

    precalculate();

    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}