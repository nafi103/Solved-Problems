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
    int n;
    cin >> n;

    vector<int> arr(n), pref(n);
    for(auto &x: arr)
        cin >> x;
    for(int i = 0; i < n; i++){
        pref[i] = arr[i];
        if(i)
            pref[i] += pref[i - 1];
    }

    int add = 0;
    for(int i = 0, j = 0; i < n; i++){
        j = max(j, i);
        while(j < n - 1){
            int inc = (j - i + 1) * (j + i + 2) - (pref[j] - (i ? pref[i - 1] : 0ll));
            int incp = (j + 1 - i + 1) * (j + 1 + i + 2) - (pref[j + 1] - (i ? pref[i - 1] : 0ll));

            if(incp > inc)
                j++;
            else
                break;
        }

        add = max(add, (j - i + 1) * (j + i + 2) - (pref[j] - (i ? pref[i - 1] : 0ll)));
    }

    cout << pref[n - 1] + add << endl;
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