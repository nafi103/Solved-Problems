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
    int n, q;
    cin >> n >> q;
    vector<vector<int>> Pr(n + 1, vector<int> (n + 1, 0)), Pc = Pr, Pm = Pr;
    for(int i = 1; i <= n; i++){
        for(int j = 1; j <= n; j++){
            cin >> Pm[i][j];
            Pr[i][j] = i * Pm[i][j];
            Pc[i][j] = j * Pm[i][j];

            Pm[i][j] += Pm[i][j - 1];
            Pm[i][j] += Pm[i - 1][j];
            Pm[i][j] -= Pm[i - 1][j - 1];

            Pr[i][j] += Pr[i][j - 1];
            Pr[i][j] += Pr[i - 1][j];
            Pr[i][j] -= Pr[i - 1][j - 1];

            Pc[i][j] += Pc[i][j - 1];
            Pc[i][j] += Pc[i - 1][j];
            Pc[i][j] -= Pc[i - 1][j - 1];
        }
    }

    auto pref_sum = [&] (vector<vector<int>> &P, int x1, int y1, int x2, int y2){
        return P[x2][y2] - P[x1 - 1][y2] - P[x2][y1 - 1] + P[x1 - 1][y1 - 1];
    };

    while(q--){
        int x1, y1, x2, y2;
        cin >> x1 >> y1 >> x2 >> y2;

        int Sr = pref_sum(Pr, x1, y1, x2, y2);
        int Sc = pref_sum(Pc, x1, y1, x2, y2);
        int Sm = pref_sum(Pm, x1, y1, x2, y2);
        int W = y2 - y1 + 1;

        cout << W * Sr + Sc + (1 - x1 * W  - y1) * Sm << " \n"[q == 0];
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}