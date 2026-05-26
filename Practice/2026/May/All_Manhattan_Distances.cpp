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

void print128(__int128_t n) {
    if (n == 0) {
        cout << 0 << endl;
        return;
    }
    string s;
    while (n > 0) {
        s += (char)('0' + (n % 10));
        n /= 10;
    }
    reverse(all(s));
    cout << s << endl;
}

void solve()
{
    int n;
    cin >> n;
    vector<int> x(n), y(n);
    for(int i = 0; i < n; i++){
        cin >> x[i] >> y[i];
    }

    sort(all(x)); sort(all(y));

    int sumx = 0, sumy = 0;
    __int128_t ans = 0;
    for(int i = 0; i < n; i++){
        ans += (x[i] * i - sumx);
        ans += (y[i] * i - sumy);

        sumx += x[i];
        sumy += y[i];
    }

    print128(ans);
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