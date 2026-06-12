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
int n;

int gap(pair<int,int> &a, pair<int,int> &b){
    return b.first - a.second;
}

int len(pair<int,int> &a){
    return a.second - a.first + 1;
}

bool valid(vector<int> &arr){
    vector<int> seg;
    for(int i = 1; i < n; i++){
        if(arr[i] != arr[i - 1]){
            seg.push_back(arr[i - 1]);
        }
    }
    seg.push_back(arr[n - 1]);
    sort(all(seg));
    for(int i = 1; i < sz(seg); i++){
        if(seg[i] == seg[i - 1])
            return false;
    }
    return true;
}

bool check(int x, int y, vector<int> &arr){
    if(x < 0 or y < 0 or x == n or y == n)
        return false;
    swap(arr[x], arr[y]);
    bool res = valid(arr);
    swap(arr[x], arr[y]);

    return res;
}

void solve()
{
    cin >> n;
    vector<vector<int>> range;
    vector<int> arr(n);

    for(int i = 0; i < n; i++){
        cin >> arr[i];
    }

    int cnt = 1;
    for(int i = 1; i < n; i++){
        if(arr[i] != arr[i - 1]){
            range.push_back({arr[i - 1], i - cnt, i - 1});
            cnt = 1;
        }else{
            cnt++;
        }
    }
    range.push_back({arr[n - 1], n - cnt, n - 1});
    sort(all(range));

    int last = range[0][0], p = 0, m = sz(range);
    while(p < m){
        vector<pair<int,int>> seg;
        while(p < m and range[p][0] == last){
            seg.push_back({range[p][1], range[p][2]});
            p++;
        }
        if(p < m)
            last = range[p][0];

        if(sz(seg) == 1)
            continue;

        if(sz(seg) > 3){
            cout << "No" << endl;
            return;
        }

        if(sz(seg) == 2){
            if(len(seg[0]) > 1 and len(seg[1]) > 1 and gap(seg[0], seg[1]) > 2){
                cout << "No" << endl;
                return;
            }

            
            if(check(seg[0].first, seg[0].second + 1, arr)
            or check(seg[1].first - 1, seg[1].second, arr)
            or check(seg[0].first, seg[1].second + 1, arr)
            or check(seg[0].first, seg[1].first - 1, arr)
            or check(seg[1].first, seg[0].second + 1, arr)
            or check(seg[1].first, seg[0].first - 1, arr)){
                cout << "Yes" << endl;
                return;
            }
            cout << "No" << endl;
            return;
        }else{
            if(len(seg[0]) > 1 and len(seg[2]) > 1){
                cout << "No" << endl;
                return;
            }

            if(check(seg[0].first, seg[1].second + 1, arr) or
                check(seg[2].first, seg[0].second + 1, arr)){
                cout << "Yes" << endl;
                return;
            }

            cout << "No" << endl;
            return;
        }
    }

    cout << "Yes" << endl;
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