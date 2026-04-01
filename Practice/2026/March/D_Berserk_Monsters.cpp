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

const int N = 3e5 + 10, not_exist = -1;
int n, a[N], d[N], Left[N], Right[N];
bool dead[N];
set<int> will_die, rip;

int find_Left(int i){
    if(i != not_exist and dead[i])
        return Left[i] = find_Left(Left[i]);
    return i;
}

int find_Right(int i){
    if(i != not_exist and dead[i])
        return Right[i] = find_Right(Right[i]);
    return i;
}

void update(int i){
    if(i == not_exist)
        return;
    Left[i] = find_Left(Left[i]);
    Right[i] = find_Right(Right[i]);
    int damage = 0;
    if(Left[i] != not_exist)
        damage += a[Left[i]];
    if(Right[i] != not_exist)
        damage += a[Right[i]];
    if(damage > d[i])
        will_die.insert(i);
}

void input(){
    cin >> n;
    for(int i = 0; i < n; i++)
        cin >> a[i];
    for(int i = 0; i < n; i++)
        cin >> d[i];
    for(int i = 0; i < n; i++){
        Left[i] = (i ? i - 1: not_exist);
        Right[i] = (i < n - 1 ? i + 1: not_exist);
        dead[i] = false;
    }
}

void solve()
{
    input();
    for(int i = 0; i < n; i++)
        update(i);
    vector<int> ans;
    while(!will_die.empty()){
        rip = will_die;
        will_die.clear();
        ans.push_back(sz(rip));
        for(auto &e: rip)
            dead[e] = true;
        for(auto &e: rip){
            Left[e] = find_Left(Left[e]);
            Right[e] = find_Right(Right[e]);
            update(Left[e]);
            update(Right[e]);
        }
    }
    for(auto &x: ans)
        cout << x << " ";
    for(int i = sz(ans); i < n; i++)
        cout << 0 << " ";
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