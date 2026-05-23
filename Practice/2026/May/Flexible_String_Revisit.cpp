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

const int N = 1e6 + 2;
int E[N], n;
void solve()
{
    cin >> n;
    string a, b;
    cin >> a >> b;
    int diff = 0;
    for(int i = 0; i < n; i++){
        if(a[i] != b[i])
            diff++;
    }
    E[n] = 1;
    for(int i = n - 1; i >= 1; i--){
        E[i] = ((n + (n - i) * E[i + 1]) % mod * inv(i)) % mod;
    }
    int ans = 0;
    for(int i = diff; i >= 1; i--){
        ans = (ans + E[i]) % mod;
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}