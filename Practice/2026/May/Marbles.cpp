#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int unsigned long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

// #ifndef ONLINE_JUDGE
// #include "debug.h"
// #define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
// #else
// #define debug(...)
// #endif

/****************************************************************/

/*
take k stars at first representing different colors

remaining stars = n - k
bars = k - 1

Formula = (n - k + k - 1)C(k - 1) -> (n - 1)C(k -1)

= (n - 1)! / (k - 1)! * (n - k)!

= O(n / 2) at max 500000 * 100 -> 500ms

nCr = nC(n - r)
*/


int nCr(int n, int r){
    int res = 1;

    for(int k = 1; k <= r; k++, n--){
        res *= n;
        if(res % k == 0)
            res /= k;
    }

    return res;
}

void solve()
{
    int n, k;
    cin >> n >> k;
    n--, k--;

    if(k < n - k)
        cout << nCr(n, k) << endl;
    else
        cout << nCr(n, n - k) << endl;
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