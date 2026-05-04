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
    int n, m, k;
    cin >> n >> m >> k;
    vector<int> arr(n);
    iota(all(arr), 1);
    if(n % m == 0){
        for(int i = 0; i < k; i++){
            int ru = n, u = n / m, j = 0;
            while(ru){
                cout << u;
                for(int k = 0; k < u; k++, j++){
                    cout << " " << arr[j];
                }
                cout << endl;
                ru -= u;
            }
        }
        return;
    }
    int u = (n + m - 1) / m, d = n / m;
    int t = n / m, rem = n - d * m;
    vector<vector<int>> table;
    table.reserve(t);
    int r = rem * u;
    for(int i = 0, flag = true; i < k; i++){
        int ru = r, rd = n - r, j = 0;
        while(ru){
            cout << u;
            for(int k = 0; k < u; k++, j++){
                cout << " " << arr[j];
            }
            cout << endl;
            ru -= u;
        }
        while(rd){
            cout << d;
            for(int k = 0; k < d; k++, j++){
                cout << " " << arr[j];
            }
            cout << endl;
            rd -= d;
        }
        reverse(arr.begin(), arr.begin() + n - r);
        reverse(arr.begin() + n - r, arr.end());
        reverse(all(arr));
        flag = flag ^ 1;
    }
    cout << "\n";
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