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
    int n, ans = 0;
    cin >> n;
    vector<int> arr(n);
    int one = 0;
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        if(arr[i] == 1)
            one++;
    }
    int color = 0;
    for(int i = 0; i < n; i++){
        if(arr[i] == 1)
            continue;
        color++;
        int two_seg = arr[i] / 2;
        int slot = two_seg - 1;
        if(one){
            int mn = min(one, slot);
            one -= mn;
            ans += mn;
        }
        ans += arr[i];
    }
    if(color == 1 and one)
        ans++;
    if(ans < 3)
        ans = 0;
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