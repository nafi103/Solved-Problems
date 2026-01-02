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

int mul(int a, int b){
    a %= mod; b %= mod;
    return ((a * b) % mod + mod) % mod;
}

int sub(int a, int b){
    a %= mod; b %= mod;
    return ((a - b) % mod + mod) % mod;
}

int add(int a, int b){
    a %= mod; b %= mod;
    return ((a + b) % mod + mod) % mod;
}

void solve()
{
    int n;
    cin >> n;
    int a[n];
    for(int i = 0; i < n; i++)
        cin >> a[i];
    sort(a, a + n);
    if(n == 1){
        cout << 0 << endl;
        return;
    }
    int pref = a[0], ans = 0, multiply = expo(2, n - 2);
    for(int i = 1; i < n; i++){
        ans = add(ans , mul(sub(mul(i , a[i]) , pref), multiply));
        pref = (pref + a[i]) % mod;
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
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}