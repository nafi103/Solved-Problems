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

bool check(int target, int one, int two, int three){
    for(int take1 = 0; take1 <= one; take1++){
        for(int take2 = 0; take2 <= two; take2++){
            int rem = target - take1 - 2 * take2;
            if(rem >= 0 and rem % 3 == 0 and rem / 3 <= three)
                return true;
        }
    }
    return false;
}

void solve()
{
    int n, mx = -inf,ans = inf;
    cin >> n;
    vector<int> arr(n);
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        mx = max(mx, arr[i]);
    }
    for(int one = 0; one <= 3; one++){
        for(int two = 0; two <= 3; two++){
            bool flag = true;
            int three = (mx - one - 2 * two + 2) / 3;
            for(int i = 0; i < n; i++){
                flag &= check(arr[i], one, two, three);
            }
            if(flag)
                ans = min(ans, one + two + three);
        }
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