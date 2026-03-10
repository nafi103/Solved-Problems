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

void solve()
{
    int n, b;
    cin >> n;
    vector<int> lock(n), suff(n + 1, 0);
    vector<pair<int,int>> full(n);
    for(int i = 0; i < n; i++){
        cin >> lock[i];
        suff[i] = lock[i];
    }
    for(int i = n - 2; i >= 0; i--){
        suff[i] += suff[i + 1];
    }
    full[0] = {lock[0], 0};
    for(int i = 1; i < n; i++){
        auto [t, extra] = full[i - 1];
        if(t + extra >= lock[i]){
            full[i] = {t, t + extra - lock[i]};
        }else{
            int pipe = i + 1;
            int rem = lock[i] - t - extra;
            int extra_time = (rem + pipe - 1) / pipe;
            full[i] = {t + extra_time, extra_time * pipe - rem};
        }
    }
    int q;
    cin >> q;
    while(q--){
        int T;
        cin >> T;
        if(T < full[n - 1].first){
            cout << -1 << endl;
            continue;
        }
        cout << (suff[0] + T - 1) / T << endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}