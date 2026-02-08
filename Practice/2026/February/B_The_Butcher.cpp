#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define h first
#define w second
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

const int N = 2e5 + 10;
int n,area;

pair<int,int> a[N];

void input(){
    area = 0;
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> a[i].h >> a[i].w;
        area += a[i].h * a[i].w;
    }
}

pair<int,int> check(){
    sort(a, a + n, greater<pair<int,int>>());
    int x = a[0].h;
    if(area % x != 0)
        return {-1, -1};
    int y = area / x;
    pair<int,int> ans = {x, y};
    multiset<pair<int,int>> hmax, wmax;
    for(int i = 0; i < n; i++){
        hmax.insert(a[i]);
        wmax.insert({a[i].w, a[i].h});
    }
    for(int i = 0; i < n - 1; i++){
        if((*hmax.rbegin()).h == x and (*hmax.rbegin()).w <= y){
            pair<int,int> tmp = *hmax.rbegin();
            y-=tmp.w;
            hmax.erase(hmax.find(tmp));
            swap(tmp.h,tmp.w);
            wmax.erase(wmax.find(tmp));
        }else if((*wmax.rbegin()).h == y and (*wmax.rbegin()).w <= x){
            pair<int,int> tmp = *wmax.rbegin();
            x-=tmp.w;
            wmax.erase(wmax.find(tmp));
            swap(tmp.h,tmp.w);
            hmax.erase(hmax.find(tmp));
        }else{
            return {-1, -1};
        }
    }
    if((*hmax.begin()) == make_pair(x, y))
        return ans;
    return {-1, -1};
}

void solve()
{
    input();
    pair<int,int> ans1 = check();
    for(int i = 0; i < n; i++)
        swap(a[i].h, a[i].w);
    pair<int,int> ans2 = check();
    swap(ans2.h, ans2.w);
    if(ans1 == ans2)
        ans2 = {-1, -1};
    int ans = 0;
    if(ans1.h != -1)
        ans++;
    if(ans2.h != -1)
        ans++;
    cout << ans << endl;
    if(ans1.h != -1)
        cout << ans1.h << " " << ans1.w << endl;
    if(ans2.h != -1)
        cout << ans2.h << " " << ans2.w << endl;
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