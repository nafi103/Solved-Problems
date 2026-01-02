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

const int N = 10010;
int n, a[N], powTwo_pref[N];

void input(){
    cin >> n;
    for(int i = 0; i < n; i++)
        cin >> a[i];
}

void solve()
{
    input();
    int ans = 0;
    for(int i = 1, pref = a[0]; i < n; i++){
        ans = (ans + ((powTwo_pref[i - 1] * a[i]) % mod) - pref + mod) % mod;
        pref = (pref * 2 + a[i]) % mod;
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

    powTwo_pref[0] = 1;
    for(int i = 1; i < N; i++){
        powTwo_pref[i] = (powTwo_pref[i - 1] * 2) % mod;
    }
    for(int i = 1; i < N; i++){
        powTwo_pref[i] = (powTwo_pref[i - 1] + powTwo_pref[i]) % mod;
    }

    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        cout<<"Case #"<<z<<": ";
        solve();
    }
}