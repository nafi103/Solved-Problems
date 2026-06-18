#include<bits/stdc++.h>
using namespace std;
 void solution()
{
    int n, arr[200001] = {0}, value = 0;
    cin>>n;
    int arr1[n];
    for (int i = 0; i < n; i++) cin>> arr1[i];
    for (int i = n-1; i >=0; i--)
    {
        arr[arr1[i]]++;
        if (arr[arr1[i]]>1){
            value = i+1;
            break;
        }
    }
    cout<<value<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}