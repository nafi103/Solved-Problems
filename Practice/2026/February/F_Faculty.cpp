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

const int N = 1e6 + 10;
int n, arr[N];

void solve()
{
    int mx_beauty = 0, mx = 0;
    cin >> n >> arr[0];
    mx = arr[0];
    cout << 0;
    for(int i = 1; i < n; i++){
        cin >> arr[i];
        if(arr[i] < 2 * mx){
            mx_beauty = max(mx_beauty, mx % arr[i] + arr[i] % mx);
            mx = max(mx, arr[i]);
        }else{
            for(int j = 0; j < i; j++){
                mx_beauty = max(mx_beauty, arr[j] % arr[i] + arr[i] % arr[j]);
            }
            mx = arr[i];
        }
        cout << " " << mx_beauty;
    }
    cout << endl;
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