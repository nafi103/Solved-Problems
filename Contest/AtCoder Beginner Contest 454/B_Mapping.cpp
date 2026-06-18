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
    int n, m;
    cin >> n >> m;
    vector<int> arr(n), cnt(m + 1, 0);
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        cnt[arr[i]]++;
    }
    sort(all(arr));
    bool flag1 = true, flag2 = true;
    for(int i = 1; i < n; i++){
        if(arr[i] == arr[i - 1])
            flag1 = false;
    }
    for(int i = 1; i <= m; i++){
        if(cnt[i] == 0)
            flag2 = false;
    }
    if(flag1)
        cout << "Yes" << endl;
    else cout << "No" << endl;
    if(flag2)
        cout << "Yes" << endl;
    else cout << "No" << endl;
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