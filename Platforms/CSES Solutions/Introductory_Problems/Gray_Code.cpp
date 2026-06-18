#include <bits/stdc++.h>
using namespace std;

#define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl '\n'
#define yes cout << "YES" << endl
#define no cout << "NO" << endl

void solve(int n)
{
    vector<string> v;
    v.push_back("0");
    v.push_back("1");
    for (int i = 2; i <= n; i++)
    {
        for (int j = v.size() - 1; j >= 0; j--)
        {
            v.push_back(v[j]);
        }
        for (int j = 0; j < v.size() / 2; j++)
        {
            v[j] = "0" + v[j];
        }
        for (int j = v.size() / 2; j < v.size(); j++)
        {
            v[j] = "1" + v[j];
        }
    }
    writev(v);
}

int main()
{
    fastIO;
    int n;
    cin >> n;
    solve(n);
}